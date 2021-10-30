




(* --------- COMREHENSIVE EXAM ITP READING COURSE 2020-21 2ND SEM --------

             Remove all the Admitted from this file by completing the proofs.

Note that before trying to work with this file you should compile the following files in the 
given order:
 1. GenReflect.v and 
 2. SetSpecs.v 
More precisely open terminal and go to the folder containing these files and type,
coqc GenReflect.v (press enter)
coqc SetSpecs.v   (press enter)  


--- Following is an overview of the functions and predicates defined in this file ----

-- In this file we would like to formalize the concept of sorting in a list.  We consider 
   lists of elements (on an arbitrary type A) with a boolean comparison operator 
   (lr: A-> A-> bool). Most of  the results in this file assumes only   
   1. reflexive, 
   2. transitive and 
   3. comparable 
   nature of the boolean operator lr. 
   Only the last result (equality of head) assumes the antisymmetric
   property of lr (i.e the comparison operator). 

   Following are the concepts formalized in this file: 

   Sorted l      <==> A Proposition to specify that l is sorted w.r.t comp operator lr 
   putin a l      ==> puts the element a into a sorted list at its correct position w.r.t lr
   sort l         ==> a function that sorts the list l w.r.t the comp operator lr 

   Some of the useful results in this file are:

   Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).

   Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).

   Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall(l: list A), Sorted (sort l).

   Lemma sort_equal (l: list A): Equal l (sort l).

   Lemma nodup_sort (l: list A): NoDup l -> NoDup (sort l). ------------------  *)



Require Export Lists.List.
Require Export GenReflect SetSpecs.
Require Export Omega.

Set Implicit Arguments.

Section Sorting.
  Context {A: Type }.

  Variable lr: A->A-> bool.
  Notation " a <=r b":= (lr a b)(at level 70, no associativity).
  
 (* ------------- sorting a list of elements by lr relation ------------------------------*)
  
  Inductive  Sorted : list A-> Prop:=
  | nil_Sorted: Sorted nil
  | cons_Sorted (a:A)(l: list A): Sorted l -> (forall x, (In x l -> (a <=r x))) -> Sorted (a::l).  

  Lemma Sorted_intro (a:A)(b:A)(l: list A)(Htrans: transitive lr):
    a <=r b -> Sorted (b::l)-> Sorted (a::b::l).
  Proof. intros H1 H2. apply cons_Sorted .  
- apply H2. 
- intros x H3 . inversion H2 . subst .  inversion H3 . rewrite <- H . apply H1. 
assert (H_e : b <=r x ) . apply H5 . apply H .
apply (Htrans b ) .
+ apply H1 .
+ apply H_e . Qed .
  Lemma Sorted_elim1 (a:A) (b:A) (l: list A): (Sorted (a::b::l)) -> (a <=r b).
  Proof. intros H . inversion H . subst . apply H3 . simpl . left . reflexivity . Qed .
  Lemma Sorted_elim4 (a:A) (l:list A): Sorted (a::l) ->(forall x, In x l -> a <=r x).
  Proof. intros . inversion H . subst . apply H4 . apply H0 . Qed .
  Lemma Sorted_elim2 (a:A) (l:list A)(Hrefl: reflexive lr):
    Sorted (a::l) ->(forall x, In x (a::l) -> a <=r x).
  Proof. intros H x H1. inversion H . subst . destruct H1 . rewrite <- H0 . apply ( Hrefl ) .
apply H4 . apply H0 . Qed .
  Lemma Sorted_elim3 (a:A) (l:list A): (Sorted (a::l)) -> Sorted l.
  Proof. intros H . inversion H . subst . apply H2 . Qed .
  Lemma Sorted_single (a:A) : (Sorted (a::nil)).
  Proof. apply cons_Sorted .
- apply nil_Sorted .
- intros  . destruct H . Qed .
  Hint Resolve Sorted_elim1 Sorted_elim2 Sorted_elim3 Sorted_elim4
       Sorted_single Sorted_intro: core.

     
  Fixpoint putin (a: A) (l: list A) : list A:=
    match l with
    |nil=> a::nil
    |b::l1 => match a <=r b with
             |true => a::l
             |false => b::(putin a l1)
                    end
    end.

  Lemma putin_intro (a:A) (l: list A): forall x, In x l -> In x (putin a l).
  Proof. intros x H . induction l  as [| b] .
- destruct H .
- simpl . case_eq ( a<=r b) .
+ intros . simpl . simpl in H . auto .
+ intros . simpl . simpl in H . destruct H .
++ auto .
++ right . apply IHl . apply H . Qed .        
  Lemma putin_intro1 (a:A) (l: list A): In a (putin a l).
  Proof. induction l . simpl . left .  reflexivity .
simpl . case_eq ( a <=r a0 ) .
+ intros . simpl  . left . reflexivity .
+ intros . simpl . right . apply IHl . Qed .
  Lemma putin_elim (a:A) (l: list A): forall x, In x (putin a l) -> (x=a)\/(In x l).
  Proof.  intros  x H. induction l .
simpl in H. simpl . intuition . simpl in H. simpl . destruct lr in H .
+ simpl in H . intuition .
+ simpl in H . destruct  H .
++ auto .
++ destruct IHl . apply H . auto . auto . Qed . 
  Definition comparable (lr: A->A-> bool) := forall x y, lr x y=false -> lr y x.
 
  Lemma putin_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall (a:A) (l: list A), Sorted l -> Sorted (putin a l).
  Proof. intros a l H. induction l . simpl . auto . simpl . inversion H . subst .
case_eq ( a <=r a0 ) .
+ intros . apply cons_Sorted . apply H . intros . destruct H1 . rewrite <- H1 . apply H0 .
apply ( H_trans a0 ) . apply H0 . apply H3 . apply H1 .
+ intros H4 . apply cons_Sorted . apply IHl . apply H2 . intros . apply putin_elim in H0 .
apply H_comp in H4 . destruct H0 . rewrite H0 . apply H4 . apply H3 . apply H0 . 
 Qed .
  
  Lemma nodup_putin (a:A)(l:list A): NoDup (a::l)-> NoDup (putin a l).
  Proof.  { revert a. induction l.
          { simpl. auto. }
          { intros a0 H. assert (Ha: NoDup (a::l)).  eauto. 
            simpl. destruct (a0 <=r a) eqn: H1. auto.
            constructor.
            { intro H2. assert ( H2a: a=a0 \/ In a l). eauto using putin_elim.
              destruct H2a. subst a. inversion H. eauto.  inversion Ha; contradiction. }
            apply IHl. inversion H. constructor; eauto.  } } Qed.

  Lemma putin_card (a:A)(l: list A): | putin a l | = S (|l|).
  Proof. { induction l.
         { simpl;auto. }
         { simpl. case (a <=r a0) eqn:H.
           simpl; auto. simpl; rewrite IHl; auto. } } Qed.
  
  
  Hint Resolve putin_intro putin_intro1 putin_elim putin_correct nodup_putin: core.


   Fixpoint sort (l: list A): list A:=
    match l with
    |nil => nil
    |a::l1 => putin a (sort l1)
    end.
  
  
  Lemma sort_intro (l: list A): forall x, In x l -> In x (sort l).
  Proof.  intros . induction l . destruct H . simpl in H .
destruct H . simpl . rewrite <- H . apply putin_intro1 . simpl . apply putin_intro . apply IHl . apply H .
Qed .

  Lemma sort_elim (l: list A): forall x, In x (sort l) -> In x l.
  Proof. intros  . induction l . simpl in H . simpl . apply H .
 simpl . simpl in H . apply putin_elim in H . destruct H . auto . right . auto . Qed .
  Lemma sort_correct (H_trans: transitive lr)(H_comp: comparable lr):
    forall(l: list A), Sorted (sort l).
  Proof. intros . induction l . simpl . apply nil_Sorted .
 simpl . apply putin_correct . auto . auto . auto . Qed .
  Hint Resolve sort_elim sort_intro sort_correct: core.
  
  

  (*--upto this point only reflexive, transitive and comparable property of <=r is needed--- *)

 
  (* ---------------------head in Sorted lists l and l'-------------------------- *)

   Definition empty: list A:= nil.
  
  Lemma empty_equal_nil_l (l: list A): l [=] empty -> l = empty.
  Proof. { case l. auto. intros s l0. unfold "[=]". intro H. 
           destruct H as [H1 H2]. absurd (In s empty). all: eauto. } Qed.


  
   (*-------- antisymmetric requirement is only needed in the following lemma--------*)
  Lemma head_equal_l (a b: A)(l s: list A)(Href: reflexive lr)(Hanti: antisymmetric lr):
    Sorted (a::l)-> Sorted (b::s)-> Equal (a::l) (b::s)-> a=b.
  Proof. { intros H H1 H2. 
         assert(H3: In b (a::l)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H3A: a <=r b). eapply Sorted_elim2;eauto.
         assert(H4: In a (b::s)).
         unfold "[=]" in H2. apply H2. auto.
         assert (H4A: b <=r a). eapply Sorted_elim2;eauto.
         eapply Hanti. split_;auto. } Qed.  

End Sorting. 



(*
 Definition l := 12::42::12::11::20::0::3::30::20::0::nil.
 Eval compute in (sort (fun x y => Nat.ltb y x) l).
 Eval compute in (sort (fun x y => ~~ (Nat.ltb x y)) l).
*)
 

