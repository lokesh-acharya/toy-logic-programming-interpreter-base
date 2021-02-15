type symbol = {op: string; ar: int};;
type signature = List of (symbol list);;

type variable = Val of int | Var of string
type term = V of variable | Node of symbol*(term list);;

type sbst = { f: string; s: term} ;; 

let s= List [{op="a";ar=0};{op="b";ar=1};{op="c";ar=2}] ;;

exception Exp of string;;

let rec sym_exist sym sl=  
  let rec check1 sym l = match l with 
  [] -> false
  | h::t -> if (h.op=sym) then 
            true
          else check1 sym t
  in

  match sl with
    List l -> check1 sym l 
;;

let rslt = sym_exist "a" s;;
Printf.printf "%b\n" rslt;;

exception DNE of string ;;

let rec check_rep sym sl= 
  let r= ref 0 in
  let rec check2 sym l= 
  if((sym_exist sym sl)=true) then  
    (match l with 
      []   -> 
              if(!r=1) then 
                true
              else 
                false
    | h::t -> begin
                if(h.op=sym) then
                  r:=!r+1
              end;
              if(!r>1) then
                false
              else
                check2 sym t)
  else raise (DNE "symbol doesn't exist\n") 
  in

  match sl with
    List l -> check2 sym l
;;

let rslt = check_rep "a" s;;
Printf.printf "%b\n" rslt;;

let rec search l x= match l with
    []-> false
  | h::t -> if(h==x) then true else search t x;;

let rec check_sig sl= 
  let cs=ref false in
  let rec check3 l =
    let sml= ref [] in  
    match l with
      []    ->  if(!cs=true) then
                  true
                else false
    | x::xs ->  begin
                  if((search !sml x.op)==false) then
                  ( sml:= !sml@[x.op];
                    if(x.ar >= 0) then
                      cs:=true;
                    if(x.ar <  0) then
                      cs:=false
                  )
                  else cs:= false
                end;

                if (!cs=true) then
                  check3 xs
                else false
  in

  match sl with
  List l -> check3 l
;; 

let rslt = check_sig s;;
Printf.printf "%b\n" rslt;;

let t= Node({op="a";ar=3},[V (Var "X"); V (Var "Y"); Node({op="c";ar=2},[V (Var "Q"); V (Var "P")])]);;

let rec size t = 
  match t with
    V x-> List.fold_left (fun n t -> n + size t) 1 []
  | Node(_,sub) -> List.fold_left (fun n t -> n + size t) 1 sub
;;

let sz= size t;;
Printf.printf "%d\n" sz;;

let lispy t =
  let opt=ref "" in
  let buf = Buffer.create 128 in
  let rec add_lispy buf = function
      V x -> (match x with
               Val a -> Buffer.add_string buf (string_of_int a)
             | Var b -> Buffer.add_string buf b)

    | Node(c, []) -> Buffer.add_string buf c.op
    | Node(c, sub) ->
       Buffer.add_string buf "(";
       Buffer.add_string buf c.op;
       List.iter (fun t -> Buffer.add_string buf " "; add_lispy buf t) sub;
       Buffer.add_string buf ")"
  in

  begin
  add_lispy buf t;
  opt:=(Buffer.contents buf);
  Printf.printf "%s\n" !opt;
  end;
  !opt
;;

let rec ht t =
  let lp= ref 0 in
  let z=lispy t in
  let i= ref ((String.length z) -1) in
  begin
    
    while(!i >= 0) do
    
      if(((String.get z !i) <> '(')=false) then
        i:= 0;

      if(((String.get z !i) <> ')')=false) then
          lp := !lp + 1;

      i:= !i-1
    
    done;
  end;
  !lp
;;

let h= ht t;;
Printf.printf "%d\n" h;;

let rec vars t= 
  let opt=ref "" in
  let buf1 = Buffer.create 128 in
  let vars_list = ref [] in
  let rec check4 buf = function
      V x -> (match x with
               Val a -> Buffer.add_string buf ""
             | Var b -> Buffer.add_string buf (b^" "))

    | Node(c, []) -> Buffer.add_string buf ""
    | Node(c, sub) -> List.iter (fun t -> Buffer.add_string buf ""; check4 buf t) sub;
  in

  begin
  check4 buf1 t;
  opt:=(Buffer.contents buf1);
  Printf.printf "%s\n" !opt;

  let i= ref ((String.length !opt) -1) in
    
  while(!i >= 0) do
      
    if(((String.get !opt !i)<>' ')=true) then
      (if((search !vars_list (String.get !opt !i))==false) then vars_list := !vars_list@[(String.get !opt !i)]);

    i:= !i -1 

  done;

  end;

  !vars_list
;;

let rec print_list = function 
[] -> Printf.printf "\n"
| e::l -> print_char e ; print_string " " ; print_list l

let h= vars t;;
print_list h;;

let s= [{f="X";s= Node({op="b";ar=2},[V(Val 1);V(Val 2)])}];;

let rec lookup x s = match s with
    []   -> V (Var x)
  | h::t -> ( if(h.f=x) then
                h.s
              else lookup x t;)
;;

let rec subst s t = 
  let rec lookup x s = match s with
    []   -> V (Var x)
  | h::t -> (if(h.f=x) then
              h.s
            else lookup x t;)
  in
  match t with
    V x ->  ( match x with
              Val a -> V (Val a) 
            | Var b -> lookup b s 
          )
  | Node(c,[])  -> Node(c,[])
  | Node(c,sub) -> Node(c,(List.map (subst s) sub)) 
;;

let z=lispy (subst s t);;

let rec p_subs (l: sbst list) = match l with
    []-> print_string "\n"
  | h::t -> print_string h.f ; print_string " " ; p_subs t
;;

let rec sub_exist (s: sbst list) (x: string) = match s with
    []   -> false
  | h::t -> if (h.f=x) then true
            else sub_exist t x
;;

let rec find_sub (s: sbst list) (x: string) = match s with
    []   -> raise (Exp "substitution for given variable DNE\n")
  | h::t -> if (h.f=x) then h.s
            else find_sub t x
;;

let rec mgu=
  let uni= ref [] in
  let rec apply2 l p =
    match p with
    ([],[]) -> !l
  | (h::[],h1::[]) -> begin mgu (h,h1) end;
                      !l
  | (h::t,h1::t1)-> begin mgu (h,h1) end;
                    apply2 l (t,t1) 
  in
  function
    (V x,V y) ->(if(x<>y) then 
                    ( match (x,y) with
                        (Var a,Var b) ->  begin
                                            if(sub_exist !uni a) then if((find_sub !uni a)<>V(Var b)) then raise (Exp "NOT_UNIFIABLE\n");
                                            if(sub_exist !uni b) then if((find_sub !uni b)<>V(Var a)) then raise (Exp "NOT_UNIFIABLE\n");
                                            if((sub_exist !uni b)=false) then uni:= !uni@[{f=b; s=(V(Var a))}];
                                            if((sub_exist !uni a)=false) then uni:= !uni@[{f=a; s=(V(Var b))}] 
                                          end; 
                                          !uni   
                      | (Var a,Val b) ->  begin
                                            if(sub_exist !uni a) then if((find_sub !uni a)<>V(Val b)) then raise (Exp "NOT_UNIFIABLE\n"); 
                                            if((sub_exist !uni a)=false) then uni:= !uni@[{f=a; s=(V(Val b))}] 
                                          end; 
                                          !uni
                      | (Val a,Var b) ->  begin 
                                            if(sub_exist !uni b) then if((find_sub !uni b)<>V(Val a)) then raise (Exp "NOT_UNIFIABLE\n");
                                            if((sub_exist !uni b)=false) then uni:= !uni@[{f=b; s=(V(Val a))}] 
                                          end;
                                          !uni
                      | (Val a,Val b) -> raise (Exp "NOT_UNIFIABLE\n")
                    )
                else !uni )
  | (Node(x,sub),V y) ->(match y with
                            Val z-> raise (Exp "NOT_UNIFIABLE\n")  
                          | Var z-> begin
                                      if(sub_exist !uni z) then if((find_sub !uni z)<>Node(x,sub)) then raise (Exp "NOT_UNIFIABLE\n");
                                      if((sub_exist !uni z)=false) then uni:= !uni@[{f=z; s=Node(x,sub)}] 
                                    end;
                                    !uni
                        )
  | (V y,Node(x,sub)) ->(match y with
                            Val z-> raise (Exp "NOT_UNIFIABLE\n")  
                          | Var z-> begin
                                      if(sub_exist !uni z) then if((find_sub !uni z)<>Node(x,sub)) then raise (Exp "NOT_UNIFIABLE\n");
                                      if((sub_exist !uni z)=false) then uni:= !uni@[{f=z; s=Node(x,sub)}] 
                                    end;
                                    !uni
                        )
  | (Node(p,q),Node(v,w)) ->( if(p.op <> v.op) then raise (Exp "NOT_UNIFIABLE\n")
                              else
                              apply2 uni (q,w) )
;;

let t1= Node({op="a";ar=3},[V (Var "X"); V (Var "Y"); Node({op="c";ar=2},[V (Var "Q"); V (Var "X")])]);;
let t2= Node({op="a";ar=3},[V (Val 1); V (Var "Y"); Node({op="c";ar=2},[V (Var "Q"); V (Val 1)])]);;

let s= [{f="X";s= Node({op="b";ar=2},[V(Val 1);V(Val 2)])}];;

let az=mgu (t1,t2);;

p_subs s;;
p_subs az;;
let z=lispy (find_sub az "X");;
let z=lispy (subst az t1);;

let rec ari sym sl=  
  let rec check5 sym l = match l with 
  [] -> -1
  | h::t -> if (h.op=sym) then 
            h.ar
          else check5 sym t
  in

  match sl with
    List l -> check5 sym l 
;;

exception Illterm of string;;

let wfterm s t=
  let cnt= ref 0 in
  let rec wft s t= 
    match t with
      V _ ->  begin
                cnt:= !cnt +1;
              end;
    | Node(x,[]) -> begin
                      if(sym_exist x.op s) then
                        if((ari x.op s)==0) then 
                          cnt:= !cnt +1
                        else raise (Illterm "ILLEGAL TERM\n")
                      else raise (Illterm "ILLEGAL TERM\n")
                    end;
    | Node(x,sub) ->  begin
                        if(sym_exist x.op s) then
                          if(x.ar==(ari x.op s)) then 
                            (
                              cnt:= !cnt +1;
                              for i=0 to (x.ar -1) do
                                wft s (List.nth sub i)
                              done
                            )
                          else raise (Illterm "ILLEGAL TERM\n")
                        else raise (Illterm "ILLEGAL TERM\n")
                      end;
  in
  begin
    wft s t
  end;
  if(!cnt==(size t)) then true
  else false 
;;

let s= List [{op="a";ar=3};{op="b";ar=1};{op="c";ar=2}] ;;
let t= Node({op="a";ar=3},[V (Var "X"); V (Var "Y"); Node({op="c";ar=2},[V (Var "Q"); V (Var "P")])]);;

let rslt = wfterm s t;;
Printf.printf "%b\n" rslt;;