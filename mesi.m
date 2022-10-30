
-- MESI 3-hop protocol

----------------------------------------------------------------------
-- Constants
----------------------------------------------------------------------
const
  ProcCount: 3;          -- number processors
  ValueCount:   3;       -- number of data values. 

  VC0: 0;                
  VC1: 1;
  VC2: 2; -- Highest priority
  NumVCs: 3; --3 channels

  NetMax: ProcCount+1;


----------------------------------------------------------------------
-- Types
----------------------------------------------------------------------
type
  Proc: scalarset(ProcCount);   -- unordered range of processors
  Value: scalarset(ValueCount); -- arbitrary values for tracking coherence #VCs=2
  Home: enum { HomeType };      -- need enumeration for IsMember calls WHY! NEED IT?
  Node: union { Home , Proc }; -- either home or proc

  Count : -3..3;
  VCType: VC0..(NumVCs-1);
  

  MessageType: enum {  GetS, -- Processor request to read a cache block
                       GetM, -- Processor request to write (get modified state)

                       PutS, -- Reply request to read a cache block
                       PutM, -- Reply request to write a cache block
                       PutE,

                       PutAck, -- Ack put request (from home)

                       FwdGetS, -- Foward the request GetS to new processor
                       FwdGetM, -- Foward the owner to new processor

                       Inv, -- Set to Invalid state
                       InvAck, -- Ack Invalid
                       
                       ExcData,
                       Data
                    };

  Message:
    Record
      mtype: MessageType;
      src: Node;
      -- do not need a destination for verification; the destination is indicated by which array entry in the Net the message is placed
      vc: VCType; --channel, direct connection
      val: Value;
      ack: Count;
    End;

  HomeState:
    Record
      state: enum { H_I, H_S, H_M, H_E, 		 --stable states
      			    H_S_D };    --transient states during recall
      owner: Node;	
      sharers: multiset [ProcCount] of Node;    --No need for sharers in this protocol, but this is a good way to represent them
      val: Value; 
    End;

  ProcState:
    Record
      state: enum { P_S, P_I, P_M, P_E, --stable states
                P_EtoI_A,
                
                P_StoI_A, 
                P_StoM_A, 
                P_StoM_AD, --T state, from S
                P_MtoI_A,  --T state from M
                P_ItoS_D,  
                P_ItoM_AD, 
                P_ItoM_A,
                P_ItoI_A --T state, from I
                };
      val: Value;
      ack: Count
    End;

----------------------------------------------------------------------
-- Variables
----------------------------------------------------------------------
var
  HomeNode:  HomeState;
  Procs: array [Proc] of ProcState;
  Net:   array [Node] of multiset [NetMax] of Message;  -- One multiset for each destination - messages are arbitrarily reordered by the multiset [buffer]
  msg_processed: boolean;
  --InBuff: array [Node] of array [VCType] of Message;
  LastWrite: Value; -- Used to confirm that writes are not lost; this variable would not exist in real hardware

----------------------------------------------------------------------
-- Procedures
----------------------------------------------------------------------
Procedure Send(mtype:MessageType;
            dst:Node;
            src:Node;
            vc:VCType;
            val:Value;
            cnt: Count;
         );

var msg:Message;

Begin
  Assert (MultiSetCount(i:Net[dst], true) < NetMax) "Too many messages"; --if !<expr> then error <string> end
  msg.mtype := mtype;
  msg.src   := src;
  msg.vc    := vc;
  msg.val   := val;
  msg.ack   := cnt;
  MultiSetAdd(msg, Net[dst]);
End;

--error handler
----------------------------------------------------
Procedure ErrorUnhandledMsg(msg:Message; n:Node);
Begin
    put "\n@@@@@@@@@@@@@@@\n";
    put "Error type : ";
    put msg.mtype;
    put "\n";
    put "source from: ";
    put msg.src;
    put " @ ";
    put n;
    put "\n";
    put "@@@@@@@@@@@@@@@@@\n";
    error "Unhandled message type!";
End;

Procedure ErrorUnhandledState();
Begin
  error "Unhandled state!";
End;

----------------------------------------------------
Procedure AddToSharersList(n:Node);
Begin
  if MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) = 0
  then
    MultiSetAdd(n, HomeNode.sharers);
  endif;
End;

Function IsSharer(n:Node) : Boolean;
Begin
  return MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) > 0
End;

Procedure RemoveFromSharersList(n:Node);
Begin
  MultiSetRemovePred(i:HomeNode.sharers, HomeNode.sharers[i] = n);
End;

-- Sends a message to all sharers except rqst
Procedure SendInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      if n != rqst
      then 
        -- Send invalidation message here 
        Send(Inv,n,rqst,VC2,UNDEFINED,MultiSetCount(i:HomeNode.sharers, true));
        --send invlidation to all 
      endif;
    endif;
  endfor;
End;

Procedure EndInvReqToSharers(rqst:Node);
Begin
  for n:Node do
    if (IsMember(n, Proc) &
        MultiSetCount(i:HomeNode.sharers, HomeNode.sharers[i] = n) != 0)
    then
      RemoveFromSharersList(n);
      if n != rqst --if requesting proc is not in S, simply remove all proc in list, 
      then 
        -- Send invalidation message here 
        Send(Inv,n,rqst,VC2,UNDEFINED,MultiSetCount(i:HomeNode.sharers, true));
        --send invlidation to all 
      endif;
    endif;
  endfor;
End;

-------------------------------------------------------
Procedure HomeReceive(msg:Message);
var cnt:0..ProcCount;  -- for counting sharers
Begin
-- Debug output may be helpful:
  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
  put " at home -- "; put HomeNode.state; put "\n";
  -- The line below is not needed in Valid/Invalid protocol.  However, the 
  -- compiler barfs if we put this inside a switch, so it is useful to
  --pre-calculate the sharer count here
  cnt := MultiSetCount(i:HomeNode.sharers, true);
  -- default to 'processing' message.  set to false otherwise

  msg_processed := true;

  switch HomeNode.state
  case H_I:
    switch msg.mtype

    case GetS:
      HomeNode.state := H_E;
      HomeNode.owner := msg.src;
      Send(ExcData, msg.src, HomeType, VC2, HomeNode.val, 0);

    case GetM: --If a write request but since no M processor, give permission
      HomeNode.state := H_M;
      HomeNode.owner := msg.src;
      Send(Data, msg.src, HomeType, VC2, HomeNode.val, 0);
    case PutM:
      Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
    case PutS:
      Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
    case PutE:
      if (msg.src != HomeNode.owner) then    
          Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
      endif;
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  case H_S:
    switch msg.mtype
    case GetS:
      AddToSharersList(msg.src);
      Send(Data, msg.src, HomeType, VC2, HomeNode.val, 0);
            
    case GetM:
        HomeNode.owner := msg.src;
        if(cnt=1 & IsSharer(msg.src)) then --when it is the only sharer
            HomeNode.state := H_M;
            RemoveFromSharersList(msg.src); -- no longer in the sharer list
            Send(Data, msg.src, HomeType, VC2, HomeNode.val, 0); --indicate it can update immediately === writeACK
        elsif(cnt != 0 & !IsSharer(msg.src)) then -- multiple sharers but req proc is not in the list, need to receive acknowledge x cnt
            HomeNode.state := H_M;
            Send(Data, msg.src, HomeType, VC2, HomeNode.val, cnt); --send data and count to requesting node (data plus cnt)
            EndInvReqToSharers(msg.src); -- invalidate all other nodes
        else --multiple sharer, one of them
            HomeNode.state := H_M;
            put cnt-1;
            put cnt;
            Send(Data, msg.src, HomeType, VC2, UNDEFINED, (cnt-1)); -- Req Proc is one of the sharer list
            EndInvReqToSharers(msg.src); -- invalidate all other nodes
        endif;

    case PutS:
        if (cnt = 1 & IsSharer(msg.src)) then
            HomeNode.state := H_I;
        endif;
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED,0); 

    case PutM:
        if (cnt = 1 & IsSharer(msg.src)) then
            HomeNode.state := H_I;
        endif;
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        RemoveFromSharersList(msg.src);
    case PutE:
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
    else
      ErrorUnhandledMsg(msg, HomeType);

    endswitch;
-------------------------------------------------------    
  case H_E:
    switch msg.mtype
    case GetS:
        AddToSharersList(HomeNode.owner);
        AddToSharersList(msg.src);
        Send(FwdGetS, HomeNode.owner, msg.src, VC2, UNDEFINED, 0);
        HomeNode.state := H_S_D;
        undefine HomeNode.owner;
    case GetM:
        Send(FwdGetM, HomeNode.owner, msg.src, VC2, UNDEFINED, 0);
        HomeNode.owner := msg.src;
        HomeNode.state := H_M;
    case PutS:
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
    case PutM:
        if (msg.src = HomeNode.owner) then
            --LastWrite := msg.val;
            HomeNode.val := msg.val;
            undefine HomeNode.owner;
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
            HomeNode.state := H_I;
        else
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        endif;
    case PutE:
        if (msg.src = HomeNode.owner) then
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
            HomeNode.owner := UNDEFINED;
            HomeNode.val := msg.val;
            HomeNode.state := H_I;
            
        else
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        endif;
    endswitch;
--------------------------------------------------------
  case H_M:
    switch msg.mtype
   
    case GetS:
        AddToSharersList(msg.src); -- add the src to sharer
        AddToSharersList(HomeNode.owner); --add when receive data
        Send(FwdGetS,HomeNode.owner,msg.src,VC2, UNDEFINED, cnt);
        HomeNode.owner := UNDEFINED; --The no owner, the old owner should evict
        
        HomeNode.state := H_S_D;
        
    case PutS:
        RemoveFromSharersList(msg.src);
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        
    case PutM:

        if(msg.src = HomeNode.owner) then
            HomeNode.owner := UNDEFINED;
            HomeNode.state := H_I;
            HomeNode.val := msg.val;
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        else
            Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        endif;
        
    case GetM:
        Send(FwdGetM, HomeNode.owner,msg.src, VC2, UNDEFINED, 0);
        HomeNode.owner := msg.src;
    case PutE:
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
    else
      ErrorUnhandledMsg(msg, HomeType);
    endswitch;

---------------------------------------------------------------    
  case H_S_D:
    switch msg.mtype
    case GetS:
        msg_processed := false;
    case GetM:
        msg_processed := false;

    case PutS:
        Send(PutAck, msg.src, HomeType, VC1, UNDEFINED, 0);
        RemoveFromSharersList(msg.src);

    case PutM:
        if(msg.src != HomeNode.owner) then --itself evit request
            Send(PutAck,msg.src, HomeType, VC1, UNDEFINED, 0);
            RemoveFromSharersList(msg.src);
        endif;

    case PutE:
        if(msg.src != HomeNode.owner) then
            RemoveFromSharersList(msg.src);
            Send(PutAck, msg.src, HomeType,VC1, UNDEFINED, 0);
        endif;

    case Data:
        HomeNode.val := msg.val;
        HomeNode.state := H_S;
    else 
        msg_processed := false;   
        ErrorUnhandledMsg(msg, HomeType);
    endswitch;

  else
    ErrorUnhandledState();
  endswitch;
End;

-----------------------------------------------------
Procedure ProcReceive(msg:Message; p:Proc);
Begin
  put "Receiving "; put msg.mtype; put " on VC"; put msg.vc; 
  put " at proc "; put p; put "\n";

  -- default to 'processing' message.  set to false otherwise
  msg_processed := true;

  alias ps:Procs[p].state do
  alias pv:Procs[p].val do
  alias pc:Procs[p].ack do

  switch ps

  case P_I:
    switch msg.mtype
    case Inv:
      put p;
      put " Just receive inv\n";
      Send(InvAck, msg.src, p, VC2, UNDEFINED,0);
    case Data:
      put "HERE we GO";
    case PutAck:
      put "Already in Invalid";
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
-------------------------------------
  case P_S:
    switch msg.mtype
    case Inv:
      ps := P_I;
      Send(InvAck, msg.src, p, VC2, UNDEFINED, 0); 
      pv := undefined;
      
    else
      ErrorUnhandledMsg(msg, p);
    endswitch;
-------------------------------------
  case P_M:    
    switch msg.mtype
    case FwdGetS:
      
      Send(Data, HomeType, p, VC2, pv, 0);
      Send(Data, msg.src, p, VC2, pv, 0);
      ps := P_S;

    case FwdGetM:
      ps := P_I;
      Send(Data, msg.src, p, VC2, pv, 0);
      undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
	endswitch;
----------------------------------
  case P_E:
    switch msg.mtype
    case FwdGetS:
        Send(Data, msg.src, p, VC2, pv, 0);
        Send(Data, HomeType, p, VC2, pv, 0);
        ps := P_S;
    case FwdGetM:
        Send(Data, msg.src, p, VC2, pv, 0);
        ps := P_I;
        undefine pv;
    else
      ErrorUnhandledMsg(msg, p);
	endswitch;
----------------------------------
  case P_ItoM_AD:
    switch msg.mtype

  	case FwdGetS:
  		msg_processed := false;
  	case FwdGetM:
  		msg_processed := false;

    case Data:
        put "Receive Data ";
        put p;
        put " from: ";
        put msg.src;
        put msg.val;
        pv := msg.val;
        if (msg.src = HomeType) then
            --pc := msg.ack;

            if(msg.ack = 0 | pc + msg.ack = 0) then --no other sharer, go directly to M
                ps := P_M;
                LastWrite := pv;
                pc := 0;
                put "Upgrade to M successfully\n";
                put "PS state: ";
                put ps;
            else
                ps := P_ItoM_A;
                put ps;
                pc := pc + msg.ack;
                put "succeed to change state to ItoM_A\n";
                put pc;
            endif;
        else --Home already in M mode
            ps := P_M;
            LastWrite := pv;
            pc := msg.ack;
        endif;

    case InvAck:
        put "IMAD case InvAck\n";
        if (pc = 1) then --All shared are now invalid
            put "1";
            ps := P_M;
            LastWrite := pv;
            pc := 0;
            put ps;
        else
            put "here";
            pc := pc - 1;
        endif;

    case PutS:
        msg_processed := false;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
 ----------------------------       
  case P_ItoM_A:
    put p; put "is now in ItoM_A\n";
    switch msg.mtype
    case FwdGetM:
        msg_processed := false;
    case FwdGetS:
        msg_processed := false;

    case InvAck:
        put "@ ItoMA";
        if (pc = 1) then --All shared are now invalid
            put "branch1";
            pc := 0;
            ps := P_M;
            LastWrite := pv;
        else
            put "branch2";
            pc := pc -1;
        endif;
    else

        ErrorUnhandledMsg(msg, p);
    endswitch;
---------------------------
  case P_ItoS_D:
    switch msg.mtype
    case ExcData:
        ps := P_E;
        pv := msg.val;
    case Data:
        ps := P_S;
        pv := msg.val;
    case Inv:
        msg_processed := false;
  	case FwdGetS:
  		msg_processed := false;
  	case FwdGetM:
  		msg_processed := false;
    else
        
        ErrorUnhandledMsg(msg, p);
    endswitch;
---------------------------
  case P_StoI_A:
    switch msg.mtype
    case Inv:
        Send(InvAck, msg.src, p, VC2, UNDEFINED, 0);
        ps := P_ItoI_A;
        undefine pv;

    case PutAck:
        ps := P_I;
        undefine pv;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
---------------------------
  case P_StoM_AD:
    switch msg.mtype
    case Data:
        put "ori ack: "; put pc;
        pv := msg.val;
        if(msg.src = HomeType) then
            if (msg.ack = 0) then
                ps:= P_M;
                pc := 0;
            else
                pc := pc + msg.ack;
                ps := P_StoM_A;
            endif;
        else
            ps := P_M;
            LastWrite := pv;
            pc := 0;
        endif;     
      
    case FwdGetS:
        msg_processed := false;
    case FwdGetM:
        msg_processed := false;
    case PutS:
        msg_processed := false;

    case InvAck:
        msg_processed:= false;

    case Inv:
        Send(InvAck, msg.src, p, VC2, UNDEFINED, 0); 
        ps := P_ItoM_AD;
        pv := undefined;
        pc := 0;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
---------------------------
  case P_StoM_A:
    switch msg.mtype           
    case FwdGetS:
        msg_processed := false;
    case FwdGetM:
        msg_processed := false;
    case PutS:
        msg_processed := false;

    case InvAck:
        pc := pc -1;
        if (pc = 0) then --All shared are now invalid
            ps := P_M;
            LastWrite := pv;    
        endif;

    case Inv:
        Send(InvAck, msg.src, p, VC2, UNDEFINED, 0); 
        ps := P_ItoM_AD;
        pv := undefined;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
---------------------------
  case P_MtoI_A:
    switch msg.mtype
    case FwdGetS:
        put "P_MtoI_A in progress";
        put pv;
        Send(Data, msg.src, p, VC2, pv, 0); --interm step, vc1
        Send(Data, HomeType, p, VC2, pv, 0);
        ps := P_StoI_A;
        
    case FwdGetM:
        Send(Data, msg.src, p, VC2, pv, 0);
        ps := P_ItoI_A; 

    case PutAck:
        ps := P_I;
        undefine pv;
        pc := 0;
    case PutM:
        put "PutM here";
        msg_processed := false;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
------------------------------
  case P_EtoI_A:
    switch msg.mtype
    case FwdGetS:
        Send(Data, msg.src, p, VC2, pv, 0);
        Send(Data, HomeType, p, VC2, pv, 0);
        ps := P_StoI_A;
    case FwdGetM:
        Send(Data, msg.src, p, VC2, pv, 0);
        ps := P_ItoI_A;
    case PutAck:
        ps := P_I;
        undefine pv;
    else
        ErrorUnhandledMsg(msg, p);
    endswitch;
------------------------------
  case P_ItoI_A:
    switch msg.mtype
    case PutAck:
        ps := P_I;
        pc := 0;
        undefine pv;
    case GetM:
        msg_processed:= false;
    case GetS:
        msg_processed := false;
    else
        ErrorUnhandledMsg(msg,p);
    endswitch;
  ----------------------------
  -- Error catch
  ----------------------------
  else
    ErrorUnhandledState();

  endswitch;

  endalias;
  endalias;
  endalias;
End;

----------------------------------------------------------------------
-- Rules
----------------------------------------------------------------------

-- Processor actions (affecting coherency)

ruleset n:Proc Do
  alias p:Procs[n] Do
	ruleset v:Value Do
--------------------------------------
    rule "store hit"
     (p.state = P_M)
        ==>
            p.val := v;
            LastWrite := v;
    endrule;
--------------------------------------
  	rule "store new value at invalid state"
   	 (p.state = P_I)
    	==>
 		   --p.val := v;  
           Send(GetM, HomeType, n, VC1, UNDEFINED,0);
 		   p.state := P_ItoM_AD;
  	endrule;
--------------------------------------
    rule "read request at I state"
     (p.state = P_I)
        ==>
            Send(GetS, HomeType, n, VC1, UNDEFINED,0);
            p.state := P_ItoS_D;
    endrule;
------------------------------------
    rule "evict Exclusive state"
     (p.state = P_E)
        ==>
            Send(PutE, HomeType, n, VC0, p.val, 0);
            p.state := P_EtoI_A;
    endrule;
------------------------------------
    rule "Request GetM at S state"
      (p.state = P_S)
        ==>
           Send(GetM, HomeType, n, VC1, UNDEFINED, 0);
           p.state := P_StoM_AD;
    endrule;
-------------------------------
    rule "store new value at E state"
      (p.state = P_E)
        ==> 
            p.val := v;
            LastWrite := v;
            p.state := P_M;
    endrule;
------------------------------
    rule "Writeback PutM"
     (p.state = P_M)
        ==> 
            put "PutM";
            Send(PutM, HomeType, n, VC0, p.val,0);
            p.state := P_MtoI_A;
    endrule;
-----------------------------
--    rule "writeback at State S"
--      (p.state = P_S)
--        ==>
--            Send(PutS, HomeType, n, VC0, UNDEFINED,0); 
--            p.state := P_StoI_A;
--    endrule;

  endruleset;  
  endalias;
endruleset;
-------------------------------
-- Message Delievery
-------------------------------
ruleset n:Node do
  choose midx:Net[n] do
    alias chan:Net[n] do
    alias msg:chan[midx] do

		-- Pick a random message in the network and delivier it
    rule "receive-net"
      (msg.vc = VC2) |
      (msg.vc = VC1 & MultiSetCount(m:chan, chan[m].vc = VC2)  = 0) |
      (msg.vc = VC0 & MultiSetCount(m:chan, chan[m].vc = VC1)  = 0 &
        MultiSetCount(m:chan, chan[m].vc = VC2)  = 0)
    ==>
      put "\n Choosed Message is: ";
      put msg.mtype;
      put " from ";
      put msg.src;
      put "\n";
      if IsMember(n, Home)
      then
        HomeReceive(msg);
		  	if msg_processed
				then
	  			MultiSetRemove(midx, chan);
				endif;
      else
        ProcReceive(msg, n);

				if msg_processed
				then
	  			MultiSetRemove(midx, chan);
				endif;
      endif;	  
    endrule;
    endalias;
    endalias;
  endchoose;  
endruleset;


----------------------------------------------------------------------
-- Startstate
----------------------------------------------------------------------
startstate

For v:Value do
  -- home node initialization
  HomeNode.state := H_I;
  undefine HomeNode.owner;
  HomeNode.val := v;
	endfor;
	LastWrite := HomeNode.val;
  
  -- processor initializatin
  for i:Proc do
    Procs[i].state := P_I;
    Procs[i].ack   := 0;
    undefine Procs[i].val;
  endfor;

  -- network initialization
  undefine Net;
endstartstate;

----------------------------------------------------------------------
-- Invariants
----------------------------------------------------------------------

invariant "Invalid implies empty owner"
  HomeNode.state = H_I
    ->
      IsUndefined(HomeNode.owner);
invariant "PC=0 when process ini M mode"
 Forall n : Proc Do	
     Procs[n].state = P_M
    ->
			Procs[n].ack = 0
	end;
invariant "value is undefined while invalid"
  Forall n : Proc Do	
     Procs[n].state = P_I
    ->
			IsUndefined(Procs[n].val)
	end;

--invariant "values in memory match last write at H_S and H_I"
--  HomeNode.state = H_I | HomeNode.state = H_S
--   ->
--    HomeNode.val = LastWrite;

--invariant "values in P_S & P_M state match last write"
--  Forall n : Proc Do	
--    Procs[n].state = P_S | Procs[n].state = P_M
--    ->
--		Procs[n].val = LastWrite --LastWrite is updated whenever a new value is created 
--	end;

--invariant " Home E must have an owner"
--    HomeNode.State = H_M
--        ->
--            HomeNode.owner = ;

invariant "values in shared state match memory"
  Forall n : Proc Do	
     HomeNode.state = H_S & Procs[n].state = P_S
    ->
			HomeNode.val = Procs[n].val
	end;

invariant "modified implies empty sharers list"
  HomeNode.state = H_M
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;

invariant "Invalid implies empty sharer list"
  HomeNode.state = H_I
    ->
      MultiSetCount(i:HomeNode.sharers, true) = 0;
