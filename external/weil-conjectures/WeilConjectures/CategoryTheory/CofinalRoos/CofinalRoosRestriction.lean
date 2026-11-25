/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictRoosModel
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Whiskering
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Limits.Shapes.Countable
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic

/-!
# Cofinal subsequence comparison of strict Roos complexes

Source: Stacks Project, Cohomology on Sites, Tag 0941, lemma-derived-limit-is-ok;
More on Algebra, Tag 0H9K, lemma-pro-isomorphism-iso-Rlim, explicit product maps.
The strict cochain refinement is the nine-step agent proof of
(blueprint: lem-fix-cofinal-roos-restriction).

Positive indices are encoded by their predecessors. Thus an order embedding `φ`
represents the positive-index function `n + 1 ↦ φ n + 1`. The two product maps
are real constructions; the theorem specifies one family of cone maps by both
coordinates, so its existential quantifier leaves no choice of cone completion.
-/

@[expose] public section

set_option autoImplicit false

universe u v uC vC r

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.CofinalRoos

/-- Restriction of complexes of strict towers along an increasing subsequence.
Source: Stacks Tag 0H9K, indices `m_n`
(blueprint: lem-fix-cofinal-roos-restriction). -/
abbrev restriction (A : Type u) [Category.{v} A] [Abelian A] (φ : ℕ ↪o ℕ) :=
  ((Functor.whiskeringLeft ℕᵒᵖ ℕᵒᵖ A).obj φ.monotone.functor.op).mapHomologicalComplex
    (ComplexShape.up ℤ)

/-- Coordinate selection `a_φ` on the source product of `1-s`.
Source: Stacks Tag 0H9K, map φ′ with identity component maps
(blueprint: lem-fix-cofinal-roos-restriction). -/
noncomputable def selection {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosP X ⟶ roosP ((restriction A φ).obj X) :=
  Pi.lift (fun n ↦ Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (φ n))

/-- Finite-block summation `b_φ`: the summand `k` has original index `φ n + k`.
Source: Stacks Tag 0H9K, map φ″ with identity component maps
(blueprint: lem-fix-cofinal-roos-restriction). -/
noncomputable def block {A : Type u} [Category.{v} A] [Abelian A]
    [HasCountableProducts A] (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosP X ⟶ roosP ((restriction A φ).obj X) :=
  Pi.lift (fun n ↦ ∑ k ∈ Finset.range (φ (n + 1) - φ n),
    Pi.π (fun i : ℕ ↦ X.asFunctor.obj (op i)) (φ n + k) ≫
      X.asFunctor.map (homOfLE (Nat.le_add_right (φ n) k)).op)

section Algebra

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable {B : Type u} [Category.{v} B] [Preadditive B] [HasCountableProducts B]

private abbrev tr (T : ℕᵒᵖ ⥤ B) (i j : ℕ) (h : i ≤ j) :=
  T.map (homOfLE h).op

private noncomputable abbrev pr (T : ℕᵒᵖ ⥤ B) (i : ℕ) :=
  Pi.π (fun n : ℕ ↦ T.obj (op n)) i

omit [Preadditive B] [HasCountableProducts B] in
private lemma tr_self (T : ℕᵒᵖ ⥤ B) (i : ℕ) : tr T i i le_rfl = 𝟙 _ := by
  simp [tr]

omit [Preadditive B] [HasCountableProducts B] in
private lemma tr_comp (T : ℕᵒᵖ ⥤ B) {i j k : ℕ} (h : i ≤ j) (h' : j ≤ k) :
    tr T j k h' ≫ tr T i j h = tr T i k (h.trans h') := by
  rw [← T.map_comp]
  rfl

private noncomputable def segment (T : ℕᵒᵖ ⥤ B) (i l : ℕ) :
    (∏ᶜ fun n : ℕ ↦ T.obj (op n)) ⟶ T.obj (op i) :=
  ∑ k ∈ Finset.range l, pr T (i + k) ≫ tr T i (i + k) (Nat.le_add_right i k)

private lemma segment_zero (T : ℕᵒᵖ ⥤ B) (i : ℕ) : segment T i 0 = 0 := by
  simp [segment]

private lemma segment_succ (T : ℕᵒᵖ ⥤ B) (i l : ℕ) :
    segment T i (l + 1) = segment T i l +
      pr T (i + l) ≫ tr T i (i + l) (Nat.le_add_right i l) := by
  exact Finset.sum_range_succ _ _

-- Reindex the middle object of a composite before simplifying transition maps.
private lemma pr_tr_eq (T : ℕᵒᵖ ⥤ B) {i j k : ℕ} (hj : i ≤ j) (hk : i ≤ k)
    (h : j = k) : pr T j ≫ tr T i j hj = pr T k ≫ tr T i k hk := by
  subst k
  rfl

private lemma segment_split (T : ℕᵒᵖ ⥤ B) (i l m : ℕ) :
    segment T i (l + m) = segment T i l +
      segment T (i + l) m ≫ tr T i (i + l) (Nat.le_add_right i l) := by
  induction m with
  | zero => simp [segment_zero]
  | succ m ih =>
    rw [← Nat.add_assoc, segment_succ, ih, segment_succ]
    simp only [Preadditive.add_comp, Category.assoc, tr_comp]
    rw [pr_tr_eq T (i := i) (j := i + (l + m)) (k := i + l + m)
      (by omega) (by omega) (Nat.add_assoc i l m).symm]
    abel

private noncomputable abbrev delta (T : ℕᵒᵖ ⥤ B) :=
  towerTransitionEndomorphism (K := fun n : ℕ ↦ T.obj (op n))
    (fun n : ℕ ↦ tr T n (n + 1) (Nat.le_succ n))

private lemma delta_pr (T : ℕᵒᵖ ⥤ B) (i : ℕ) :
    delta T ≫ pr T i = pr T i - pr T (i + 1) ≫
      tr T i (i + 1) (Nat.le_succ i) := by
  simp [delta, towerTransitionEndomorphism, towerProductShift]

private lemma delta_segment (T : ℕᵒᵖ ⥤ B) (i l : ℕ) :
    delta T ≫ segment T i l = pr T i - pr T (i + l) ≫
      tr T i (i + l) (Nat.le_add_right i l) := by
  induction l with
  | zero => simp [segment_zero, tr_self]
  | succ l ih =>
    rw [segment_succ, Preadditive.comp_add, ih, ← Category.assoc, delta_pr]
    simp only [Preadditive.sub_comp, Category.assoc, tr_comp]
    abel

-- The least selected index lying above i, including the initial unselected block.
private noncomputable def ceiling (φ : ℕ ↪o ℕ) (i : ℕ) : ℕ :=
  Nat.find (show ∃ n, i ≤ φ n from ⟨i, φ.strictMono.le_apply⟩)

private lemma ceiling_le (φ : ℕ ↪o ℕ) (i : ℕ) : i ≤ φ (ceiling φ i) :=
  by
    unfold ceiling
    exact Nat.find_spec (show ∃ n, i ≤ φ n from ⟨i, φ.strictMono.le_apply⟩)

private lemma ceiling_min (φ : ℕ ↪o ℕ) {i n : ℕ} (h : i ≤ φ n) :
    ceiling φ i ≤ n := Nat.find_min' _ h

private lemma ceiling_selected (φ : ℕ ↪o ℕ) (n : ℕ) : ceiling φ (φ n) = n := by
  apply Nat.le_antisymm (ceiling_min φ le_rfl)
  exact φ.le_iff_le.mp (ceiling_le φ (φ n))

private lemma ceiling_between (φ : ℕ ↪o ℕ) {i n : ℕ}
    (hi : φ n < i) (hi' : i ≤ φ (n + 1)) : ceiling φ i = n + 1 := by
  apply Nat.le_antisymm (ceiling_min φ hi')
  have h := ceiling_le φ i
  have : n < ceiling φ i := φ.lt_iff_lt.mp (hi.trans_le h)
  omega

private lemma ceiling_next (φ : ℕ ↪o ℕ) (i : ℕ) (hi : i < φ (ceiling φ i)) :
    ceiling φ (i + 1) = ceiling φ i := by
  apply Nat.le_antisymm (ceiling_min φ hi)
  exact ceiling_min φ ((Nat.le_succ i).trans (ceiling_le φ (i + 1)))

private abbrev subTower (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) : ℕᵒᵖ ⥤ B where
  obj n := T.obj (op (φ n.unop))
  map f := T.map (homOfLE (φ.monotone (leOfHom f.unop))).op
  map_id n := by simp
  map_comp f g := by rw [← T.map_comp]; rfl

private lemma sub_pr_tr_eq (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) {i n m : ℕ}
    (hn : i ≤ φ n) (hm : i ≤ φ m) (h : n = m) :
    pr (subTower T φ) n ≫ tr T i (φ n) hn =
      pr (subTower T φ) m ≫ tr T i (φ m) hm := by
  subst m
  rfl

private lemma segment_tr_eq (T : ℕᵒᵖ ⥤ B) {i j k l : ℕ}
    (hj : i ≤ j) (hk : i ≤ k) (h : j = k) :
    segment T j l ≫ tr T i j hj = segment T k l ≫ tr T i k hk := by
  subst k
  rfl

private noncomputable def chooseMap (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    (∏ᶜ fun i : ℕ ↦ T.obj (op i)) ⟶ (∏ᶜ fun n : ℕ ↦ (subTower T φ).obj (op n)) :=
  Pi.lift (fun n ↦ pr T (φ n))

private noncomputable def sumMap (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    (∏ᶜ fun i : ℕ ↦ T.obj (op i)) ⟶ (∏ᶜ fun n : ℕ ↦ (subTower T φ).obj (op n)) :=
  Pi.lift (fun n ↦ segment T (φ n) (φ (n + 1) - φ n))

-- Extend compatible coordinates by the transition from the next selected index.
private noncomputable def extendMap (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    (∏ᶜ fun n : ℕ ↦ (subTower T φ).obj (op n)) ⟶ (∏ᶜ fun i : ℕ ↦ T.obj (op i)) :=
  Pi.lift (fun i ↦ pr (subTower T φ) (ceiling φ i) ≫
    tr T i (φ (ceiling φ i)) (ceiling_le φ i))

-- Put zero in every coordinate outside the image of the subsequence.
private noncomputable def insertMap (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    (∏ᶜ fun n : ℕ ↦ (subTower T φ).obj (op n)) ⟶ (∏ᶜ fun i : ℕ ↦ T.obj (op i)) :=
  Pi.lift (fun i ↦ if i = φ (ceiling φ i) then
    pr (subTower T φ) (ceiling φ i) ≫ tr T i (φ (ceiling φ i)) (ceiling_le φ i)
    else 0)

-- A finite sum, even when the first selected index is positive.
private noncomputable def contractMap (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    (∏ᶜ fun i : ℕ ↦ T.obj (op i)) ⟶ (∏ᶜ fun i : ℕ ↦ T.obj (op i)) :=
  Pi.lift (fun i ↦ segment T i (φ (ceiling φ i) - i))

private lemma choose_pr (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (n : ℕ) :
    chooseMap T φ ≫ pr (subTower T φ) n = pr T (φ n) := Pi.lift_comp_π _ _

private lemma sum_pr (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (n : ℕ) :
    sumMap T φ ≫ pr (subTower T φ) n =
      segment T (φ n) (φ (n + 1) - φ n) := Pi.lift_comp_π _ _

private lemma extend_pr (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (i : ℕ) :
    extendMap T φ ≫ pr T i = pr (subTower T φ) (ceiling φ i) ≫
      tr T i (φ (ceiling φ i)) (ceiling_le φ i) := Pi.lift_comp_π _ _

private lemma extend_selected (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (n : ℕ) :
    extendMap T φ ≫ pr T (φ n) = pr (subTower T φ) n := by
  rw [extend_pr]
  calc
    _ = pr (subTower T φ) n ≫ tr T (φ n) (φ n) le_rfl :=
      sub_pr_tr_eq T φ _ _ (ceiling_selected φ n)
    _ = _ := by rw [tr_self, Category.comp_id]

private lemma insert_pr (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (i : ℕ) :
    insertMap T φ ≫ pr T i = if i = φ (ceiling φ i) then
      pr (subTower T φ) (ceiling φ i) ≫
        tr T i (φ (ceiling φ i)) (ceiling_le φ i) else 0 := Pi.lift_comp_π _ _

private lemma contract_pr (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (i : ℕ) :
    contractMap T φ ≫ pr T i = segment T i (φ (ceiling φ i) - i) := Pi.lift_comp_π _ _

private lemma square (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    delta T ≫ sumMap T φ = chooseMap T φ ≫ delta (subTower T φ) := by
  with_unfolding_all
    apply Pi.hom_ext
    intro n
    change (delta T ≫ sumMap T φ) ≫ pr (subTower T φ) n =
      (chooseMap T φ ≫ delta (subTower T φ)) ≫ pr (subTower T φ) n
    simp only [Category.assoc]
    rw [sum_pr, delta_segment, delta_pr, Preadditive.comp_sub,
      ← Category.assoc, choose_pr, choose_pr]
    have hi : φ n + (φ (n + 1) - φ n) = φ (n + 1) :=
      Nat.add_sub_of_le (φ.monotone (Nat.le_succ n))
    exact congrArg (fun f ↦ pr T (φ n) - f)
      (pr_tr_eq T _ _ hi)

private lemma choose_extend (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    extendMap T φ ≫ chooseMap T φ = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  change (extendMap T φ ≫ chooseMap T φ) ≫ pr (subTower T φ) n = _
  rw [Category.assoc, choose_pr, extend_pr]
  rw [Category.id_comp]
  calc
    _ = pr (subTower T φ) n ≫ tr T (φ n) (φ n) le_rfl :=
      sub_pr_tr_eq T φ _ _ (ceiling_selected φ n)
    _ = _ := by rw [tr_self, Category.comp_id]

private lemma contract_delta (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    delta T ≫ contractMap T φ = 𝟙 _ - chooseMap T φ ≫ extendMap T φ := by
  with_unfolding_all
    apply Pi.hom_ext
    intro i
    change (delta T ≫ contractMap T φ) ≫ pr T i = _
    rw [Category.assoc, contract_pr, delta_segment]
    rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, extend_pr,
      ← Category.assoc, choose_pr]
    have hi : i + (φ (ceiling φ i) - i) = φ (ceiling φ i) :=
      Nat.add_sub_of_le (ceiling_le φ i)
    exact congrArg (fun f ↦ pr T i - f) (pr_tr_eq T _ _ hi)

private lemma insert_selected (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (n : ℕ) :
    insertMap T φ ≫ pr T (φ n) = pr (subTower T φ) n := by
  rw [insert_pr, ite_eq_left (by rw [ceiling_selected])]
  calc
    _ = pr (subTower T φ) n ≫ tr T (φ n) (φ n) le_rfl :=
      sub_pr_tr_eq T φ _ _ (ceiling_selected φ n)
    _ = _ := by rw [tr_self, Category.comp_id]

private lemma insert_between (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) {i n : ℕ}
    (hi : φ n < i) (hi' : i < φ (n + 1)) : insertMap T φ ≫ pr T i = 0 := by
  rw [insert_pr, ite_eq_right]
  rw [ceiling_between φ hi hi'.le]
  omega

private lemma sum_insert (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    insertMap T φ ≫ sumMap T φ = 𝟙 _ := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, sumMap, Pi.lift_comp_π, Category.id_comp, segment,
    Preadditive.comp_sum]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.add_zero, insert_selected, tr_self, Category.comp_id]
  · intro k hk hk0
    have hk' := Finset.mem_range.mp hk
    have hm : φ n < φ (n + 1) := φ.strictMono (Nat.lt_succ_self n)
    rw [← Category.assoc, insert_between T φ (n := n) (by omega) (by omega),
      Limits.zero_comp]
  · intro hn
    have hm : φ n < φ (n + 1) := φ.strictMono (Nat.lt_succ_self n)
    exact False.elim (hn (Finset.mem_range.mpr (by omega)))

private lemma extend_square (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    extendMap T φ ≫ delta T = delta (subTower T φ) ≫ insertMap T φ := by
  with_unfolding_all
    apply Pi.hom_ext
    intro i
    change (extendMap T φ ≫ delta T) ≫ pr T i = _
    by_cases hi : i = φ (ceiling φ i)
    · obtain ⟨n, rfl⟩ : ∃ n, i = φ n := ⟨ceiling φ i, hi⟩
      have hc : ceiling φ (φ n + 1) = n + 1 :=
        ceiling_between φ (Nat.lt_succ_self _) (φ.strictMono (Nat.lt_succ_self n))
      have he : extendMap T φ ≫ pr T (φ n + 1) =
          pr (subTower T φ) (n + 1) ≫
            tr T (φ n + 1) (φ (n + 1)) (φ.strictMono (Nat.lt_succ_self n)) := by
        rw [extend_pr]
        exact sub_pr_tr_eq T φ _ _ hc
      rw [Category.assoc, delta_pr, Preadditive.comp_sub, extend_selected,
        ← Category.assoc, he, Category.assoc, tr_comp, Category.assoc,
        insert_selected, delta_pr]
    · have hlt : i < φ (ceiling φ i) := lt_of_le_of_ne (ceiling_le φ i) hi
      rw [Category.assoc, delta_pr, Preadditive.comp_sub, ← Category.assoc,
        extend_pr, extend_pr, Category.assoc, tr_comp, Category.assoc,
        insert_pr, ite_eq_right hi, Limits.comp_zero]
      exact sub_eq_zero.mpr
        (sub_pr_tr_eq T φ _ _ (ceiling_next φ i hlt).symm)

private lemma segment_first (T : ℕᵒᵖ ⥤ B) (i l : ℕ) :
    segment T i (l + 1) = pr T i +
      segment T (i + 1) l ≫ tr T i (i + 1) (Nat.le_succ i) := by
  simpa only [segment, Finset.sum_range_one, Nat.add_zero, tr_self,
    Category.comp_id, Nat.add_comm 1 l] using segment_split T i 1 l

private lemma delta_contract (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) :
    contractMap T φ ≫ delta T = 𝟙 _ - sumMap T φ ≫ insertMap T φ := by
  with_unfolding_all
    apply Pi.hom_ext
    intro i
    change (contractMap T φ ≫ delta T) ≫ pr T i = _
    rw [Category.assoc, delta_pr, Preadditive.comp_sub, ← Category.assoc,
      contract_pr, contract_pr]
    by_cases hi : i = φ (ceiling φ i)
    · obtain ⟨n, rfl⟩ : ∃ n, i = φ n := ⟨ceiling φ i, hi⟩
      have hc : ceiling φ (φ n + 1) = n + 1 :=
        ceiling_between φ (Nat.lt_succ_self _) (φ.strictMono (Nat.lt_succ_self n))
      simp only [ceiling_selected, hc, Nat.sub_self, segment_zero]
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, insert_selected, sum_pr]
      have hm : φ n < φ (n + 1) := φ.strictMono (Nat.lt_succ_self n)
      have hd : φ (n + 1) - φ n = (φ (n + 1) - (φ n + 1)) + 1 := by omega
      rw [hd, segment_first]
      abel
    · have hlt : i < φ (ceiling φ i) := lt_of_le_of_ne (ceiling_le φ i) hi
      rw [Preadditive.sub_comp, Category.id_comp, Category.assoc, insert_pr,
        ite_eq_right hi, Limits.comp_zero, sub_zero]
      simp_rw [ceiling_next φ i hlt]
      have hd : φ (ceiling φ i) - i = (φ (ceiling φ i) - (i + 1)) + 1 := by omega
      rw [hd, segment_first]
      abel

private lemma choose_natural {T U : ℕᵒᵖ ⥤ B} (f : T ⟶ U) (φ : ℕ ↪o ℕ) :
    Limits.Pi.map (fun n : ℕ ↦ f.app (op n)) ≫ chooseMap U φ =
      chooseMap T φ ≫ Limits.Pi.map (fun n : ℕ ↦ f.app (op (φ n))) := by
  apply Pi.hom_ext
  intro n
  simp [chooseMap, pr]

private lemma sum_natural {T U : ℕᵒᵖ ⥤ B} (f : T ⟶ U) (φ : ℕ ↪o ℕ) :
    Limits.Pi.map (fun n : ℕ ↦ f.app (op n)) ≫ sumMap U φ =
      sumMap T φ ≫ Limits.Pi.map (fun n : ℕ ↦ f.app (op (φ n))) := by
  with_unfolding_all
    apply Pi.hom_ext
    intro n
    change (Limits.Pi.map (fun n : ℕ ↦ f.app (op n)) ≫ sumMap U φ) ≫
        Pi.π (fun n : ℕ ↦ U.obj (op (φ n))) n =
      (sumMap T φ ≫ Limits.Pi.map (fun n : ℕ ↦ f.app (op (φ n)))) ≫
        Pi.π (fun n : ℕ ↦ U.obj (op (φ n))) n
    simp only [sumMap, Category.assoc, Pi.lift_comp_π, Pi.map_π, Pi.lift_comp_π_assoc,
      segment, Preadditive.comp_sum, Preadditive.sum_comp]
    apply Finset.sum_congr rfl
    intro k hk
    simp only [← Category.assoc, pr, Pi.map_π, Category.assoc]
    rw [f.naturality]
    rw [Pi.map_π_assoc]

private lemma choose_comp (T : ℕᵒᵖ ⥤ B) (φ ψ : ℕ ↪o ℕ) :
    chooseMap T φ ≫ chooseMap (subTower T φ) ψ = chooseMap T (ψ.trans φ) := by
  apply Pi.hom_ext
  intro n
  simp [chooseMap, pr]

private lemma sum_segment (T : ℕᵒᵖ ⥤ B) (φ : ℕ ↪o ℕ) (n l : ℕ) :
    sumMap T φ ≫ segment (subTower T φ) n l =
      segment T (φ n) (φ (n + l) - φ n) := by
  with_unfolding_all
    induction l with
    | zero => simp [segment_zero]
    | succ l ih =>
      rw [segment_succ, Preadditive.comp_add, ih, ← Category.assoc]
      change segment T (φ n) (φ (n + l) - φ n) +
        (sumMap T φ ≫ pr (subTower T φ) (n + l)) ≫
          tr T (φ n) (φ (n + l)) (φ.monotone (Nat.le_add_right n l)) = _
      rw [sum_pr]
      have h₁ := φ.monotone (Nat.le_add_right n l)
      have h₂ := φ.monotone (show n + l ≤ n + l + 1 by omega)
      have he : φ (n + (l + 1)) - φ n =
          (φ (n + l) - φ n) + (φ (n + l + 1) - φ (n + l)) := by
        have hn : n + (l + 1) = n + l + 1 := by omega
        rw [hn]
        omega
      rw [he]
      have hi : φ n + (φ (n + l) - φ n) = φ (n + l) := Nat.add_sub_of_le h₁
      rw [segment_split]
      exact congrArg (fun f ↦ segment T (φ n) (φ (n + l) - φ n) + f)
        (segment_tr_eq T _ _ hi).symm

private lemma sum_comp (T : ℕᵒᵖ ⥤ B) (φ ψ : ℕ ↪o ℕ) :
    sumMap T φ ≫ sumMap (subTower T φ) ψ = sumMap T (ψ.trans φ) := by
  with_unfolding_all
    apply Pi.hom_ext
    intro n
    change (sumMap T φ ≫ sumMap (subTower T φ) ψ) ≫
        pr (subTower (subTower T φ) ψ) n = sumMap T (ψ.trans φ) ≫
          pr (subTower T (ψ.trans φ)) n
    rw [Category.assoc, sum_pr, sum_segment, sum_pr]
    have hi : ψ n + (ψ (n + 1) - ψ n) = ψ (n + 1) :=
      Nat.add_sub_of_le (ψ.monotone (Nat.le_succ n))
    simp only [hi]
    rfl

end Algebra

section Complexes

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types true

variable {A : Type u} [Category.{v} A] [Abelian A] [HasCountableProducts A]

private theorem complexProducts : HasCountableProducts (CochainComplex A ℤ) := by
  constructor
  intro K _
  have : HasLimitsOfShape (Discrete K) A := inferInstance
  infer_instance

attribute [local instance] complexProducts

private lemma block_square (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosU X ≫ block X φ = selection X φ ≫ roosU ((restriction A φ).obj X) :=
  square X.asFunctor φ

private noncomputable def squareMap {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a b : roosP X ⟶ roosP Y) (w : roosU X ≫ b = a ≫ roosU Y) :
    roosF.obj X ⟶ roosF.obj Y :=
  (CochainComplex.mappingCone.map (roosU X) (roosU Y) a b w)⟦(-1 : ℤ)⟧'

private lemma squareMap_congr {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    {a a' b b' : roosP X ⟶ roosP Y} (ha : a = a') (hb : b = b')
    (w : roosU X ≫ b = a ≫ roosU Y) (w' : roosU X ≫ b' = a' ≫ roosU Y) :
    squareMap a b w = squareMap a' b' w' := by
  subst a'
  subst b'
  rfl

private lemma squareMap_coord {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a b : roosP X ⟶ roosP Y) (w : roosU X ≫ b = a ≫ roosU Y) (p : ℤ) :
    (squareMap a b w).f (p + 1) ≫ (roosχ Y p).hom =
      (roosχ X p).hom ≫ biprod.map (b.f p) (a.f (p + 1)) := by
  with_unfolding_all
    dsimp only [squareMap, roosχ, Iso.trans_hom]
    rw [CochainComplex.shiftFunctor_map_f']
    simp only [Category.assoc, CochainComplex.shiftFunctorObjXIso]
    dsimp only [roosF, Functor.comp_obj, roosConeFunctor]
    rw [HomologicalComplex.XIsoOfEq_hom_naturality_assoc]
    congr 1
    apply CochainComplex.mappingCone.ext_from (roosU X) (p + 1) p rfl
    · change (CochainComplex.mappingCone.inl (roosU X)).v (p + 1) p (by omega) ≫
          (CochainComplex.mappingCone.map _ _ a b w).f p ≫ _ = _
      simp only [CochainComplex.mappingCone.map,
        CochainComplex.mappingCone.inl_v_desc_f_assoc,
        CochainComplex.HomComplex.Cochain.zero_cochain_comp_v]
      simp only [CochainComplex.mappingCone.inl,
        CochainComplex.HomComplex.Cochain.mk_v, Category.assoc,
        HomologicalComplex.homotopyCofiber.inlX_XIsoBiprod_hom_assoc]
      apply biprod.hom_ext <;> simp
    · rw [CochainComplex.mappingCone.map,
        CochainComplex.mappingCone.inr_f_desc_f_assoc]
      simp only [HomologicalComplex.comp_f, CochainComplex.mappingCone.inr, Category.assoc]
      apply biprod.hom_ext <;> simp

private noncomputable def rho (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    roosF.obj X ⟶ roosF.obj ((restriction A φ).obj X) :=
  squareMap (selection X φ) (block X φ) (block_square X φ)

private lemma rho_coord (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) (p : ℤ) :
    (rho X φ).f (p + 1) ≫ (roosχ ((restriction A φ).obj X) p).hom =
      (roosχ X p).hom ≫ biprod.map ((block X φ).f p) ((selection X φ).f (p + 1)) :=
  squareMap_coord _ _ _ p

private lemma squareMap_comp {X Y Z : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (a b : roosP X ⟶ roosP Y) (w : roosU X ≫ b = a ≫ roosU Y)
    (c d : roosP Y ⟶ roosP Z) (w' : roosU Y ≫ d = c ≫ roosU Z) :
    squareMap a b w ≫ squareMap c d w' =
      squareMap (a ≫ c) (b ≫ d)
        (by rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) := by
  unfold squareMap
  rw [← Functor.map_comp, ← CochainComplex.mappingCone.map_comp]

private lemma rho_natural {X Y : CochainComplex (ℕᵒᵖ ⥤ A) ℤ}
    (f : X ⟶ Y) (φ : ℕ ↪o ℕ) :
    roosF.map f ≫ rho Y φ = rho X φ ≫ roosF.map ((restriction A φ).map f) := by
  with_unfolding_all
    change squareMap (roosPmap f) (roosPmap f) (roosU_natural f) ≫ rho Y φ =
      rho X φ ≫ squareMap _ _ (roosU_natural ((restriction A φ).map f))
    unfold rho
    rw [squareMap_comp, squareMap_comp]
    have ha : roosPmap f ≫ selection Y φ =
        selection X φ ≫ roosPmap ((restriction A φ).map f) :=
      choose_natural (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) φ
    have hb : roosPmap f ≫ block Y φ =
        block X φ ≫ roosPmap ((restriction A φ).map f) :=
      sum_natural (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map f) φ
    exact squareMap_congr ha hb _ _

private lemma rho_comp (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ ψ : ℕ ↪o ℕ) :
    HEq (rho X φ ≫ rho ((restriction A φ).obj X) ψ) (rho X (ψ.trans φ)) := by
  with_unfolding_all
    apply heq_of_eq
    unfold rho
    rw [squareMap_comp]
    have ha : selection X φ ≫ selection ((restriction A φ).obj X) ψ =
        selection X (ψ.trans φ) := choose_comp X.asFunctor φ ψ
    have hb : block X φ ≫ block ((restriction A φ).obj X) ψ =
        block X (ψ.trans φ) := sum_comp X.asFunctor φ ψ
    exact squareMap_congr ha hb _ _

omit [HasCountableProducts A] in
private noncomputable def coneContract (P : CochainComplex A ℤ) (d c e h : P ⟶ P)
    (w : d ≫ e = c ≫ d) (h₁ : d ≫ h = 𝟙 P - c) (h₂ : h ≫ d = 𝟙 P - e) :
    Homotopy (𝟙 (CochainComplex.mappingCone d))
      (CochainComplex.mappingCone.map d d c e w) := by
  open CochainComplex CochainComplex.HomComplex in
  refine mappingCone.descHomotopy d _ _ 0
    ((Cochain.ofHom h).comp (mappingCone.inl d) (zero_add _)) ?_ ?_
  · ext p q hpq
    have hp : p = q + 1 := by omega
    subst p
    simp only [Cochain.comp_zero_cochain_v, Cochain.ofHom_v,
      HomologicalComplex.id_f, Category.comp_id, δ_zero, Cochain.zero_v,
      zero_add, Cochain.add_v, Cochain.zero_cochain_comp_v,
      mappingCone.map, mappingCone.inl_v_desc_f]
    have hh := congrArg (fun f : P ⟶ P ↦ f.f (q + 1)) h₁
    simp only [HomologicalComplex.comp_f, HomologicalComplex.sub_f_apply,
      HomologicalComplex.id_f] at hh
    rw [← Category.assoc, hh, Preadditive.sub_comp, Category.id_comp]
    abel
  · simp only [Category.comp_id, δ_ofHom_comp, mappingCone.δ_inl,
      ← Cochain.ofHom_comp, mappingCone.map, mappingCone.inr_desc]
    rw [← Category.assoc, h₂, Preadditive.sub_comp, Category.id_comp,
      Cochain.ofHom_sub]
    abel

-- The product contraction gives a homotopy equivalence before shifting.
private lemma rho_quasiIso (X : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) (φ : ℕ ↪o ℕ) :
    QuasiIso (rho X φ) := by
  with_unfolding_all
    let Y := (restriction A φ).obj X
    let a : roosP X ⟶ roosP Y := selection X φ
    let b : roosP X ⟶ roosP Y := block X φ
    let e : roosP Y ⟶ roosP X := extendMap X.asFunctor φ
    let j : roosP Y ⟶ roosP X := insertMap X.asFunctor φ
    let h : roosP X ⟶ roosP X := contractMap X.asFunctor φ
    have w : roosU X ≫ b = a ≫ roosU Y := block_square X φ
    have w' : roosU Y ≫ j = e ≫ roosU X := (extend_square X.asFunctor φ).symm
    have ha : e ≫ a = 𝟙 _ := choose_extend X.asFunctor φ
    have hb : j ≫ b = 𝟙 _ := sum_insert X.asFunctor φ
    have hh₁ : roosU X ≫ h = 𝟙 _ - a ≫ e := contract_delta X.asFunctor φ
    have hh₂ : h ≫ roosU X = 𝟙 _ - b ≫ j := delta_contract X.asFunctor φ
    let c := CochainComplex.mappingCone.map (roosU X) (roosU Y) a b w
    let s := CochainComplex.mappingCone.map (roosU Y) (roosU X) e j w'
    have hcs : c ≫ s = CochainComplex.mappingCone.map (roosU X) (roosU X)
        (a ≫ e) (b ≫ j) (by rw [← Category.assoc, w, Category.assoc, w', Category.assoc]) :=
      (CochainComplex.mappingCone.map_comp (roosU X) (roosU Y) (roosU X)
        a b w e j w').symm
    have hsc : s ≫ c = 𝟙 _ := by
      dsimp only [s, c]
      rw [← CochainComplex.mappingCone.map_comp]
      simpa only [ha, hb] using CochainComplex.mappingCone.map_id (roosU Y)
    let equiv : HomotopyEquiv (CochainComplex.mappingCone (roosU X))
        (CochainComplex.mappingCone (roosU Y)) :=
      { hom := c
        inv := s
        homotopyHomInvId := (Homotopy.ofEq hcs).trans
          (coneContract (roosP X) (roosU X) (a ≫ e) (b ≫ j) h _ hh₁ hh₂).symm
        homotopyInvHomId := Homotopy.ofEq hsc }
    have hc : QuasiIso c := equiv.quasiIso_hom
    exact (CochainComplex.quasiIso_shift_iff c (-1)).mpr hc

end Complexes

end CategoryTheory.CofinalRoos
