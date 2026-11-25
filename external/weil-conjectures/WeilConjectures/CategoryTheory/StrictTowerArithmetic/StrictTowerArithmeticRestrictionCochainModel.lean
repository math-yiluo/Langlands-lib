/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.StrictTowerArithmetic.StrictTowerArithmeticRestrictionDefs
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import WeilConjectures.CategoryTheory.TowerSplitEnvelope
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # The explicit arithmetic map between cochain Roos models

Source: Stacks Project, Tags 0941, 070M and 0H9K.
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

@[expose] public section

set_option autoImplicit false
universe a b
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.StrictTowerArithmetic

private lemma telescoping
    {D : Type*} [Category D] [Preadditive D]
    (X : ℕᵒᵖ ⥤ D) [HasProduct (fun i : ℕ ↦ X.obj (op i))] (s m : ℕ) :
    (∑ k ∈ Finset.range m,
      (Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + k) -
        Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + k + 1) ≫
          X.map (homOfLE (Nat.le_succ (s + k))).op) ≫
        X.map (homOfLE (Nat.le_add_right s k)).op) =
      Pi.π (fun i : ℕ ↦ X.obj (op i)) s -
        Pi.π (fun i : ℕ ↦ X.obj (op i)) (s + m) ≫
          X.map (homOfLE (Nat.le_add_right s m)).op := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    have hcomp : X.map (homOfLE (Nat.le_succ (s + m))).op ≫
        X.map (homOfLE (Nat.le_add_right s m)).op =
        X.map (homOfLE (Nat.le_add_right s (m + 1))).op := by
      rw [← X.map_comp]
      rfl
    simp only [Preadditive.sub_comp, Category.assoc, hcomp]
    abel

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma block_square
    {A : Type a} [Category.{b} A] [Abelian A] [HasCountableProducts A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    boundary I ≫ block e I.asFunctor =
      selection e I.asFunctor ≫ boundary ((complexRestriction _ e).obj I) := by
  apply Pi.hom_ext
  intro n
  let s := e * (n + 1) - 1
  have hnext : s + e = e * (n + 1 + 1) - 1 := by
    dsimp [s]
    rw [Nat.mul_succ e (n + 1)]
    have : 1 ≤ e * (n + 1) := by nlinarith
    omega
  let X := I.asFunctor
  change (towerTransitionEndomorphism (fun n : ℕ ↦
      X.map (homOfLE (Nat.le_succ n)).op) ≫ block e X) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n =
    (selection e X ≫ towerTransitionEndomorphism (fun n : ℕ ↦
      X.map ((index e).map (homOfLE (Nat.le_succ n)).op))) ≫
      Pi.π (fun n : ℕ ↦ X.obj ((index e).obj (op n))) n
  simp only [block, selection, towerTransitionEndomorphism,
    towerProductShift, Category.assoc, Pi.lift_comp_π, Preadditive.comp_sub,
    Category.comp_id, Preadditive.comp_sum, Preadditive.sub_comp,
    Category.id_comp, Pi.lift_comp_π_assoc]
  have ht := telescoping X s e
  simp only [Preadditive.sub_comp, Category.assoc, Finset.sum_sub_distrib] at ht
  dsimp only [s] at ht hnext
  convert ht using 1
  · rfl
  · congr 1
    have hcongr (k l : ℕ) (hk : s ≤ k) (hl : s ≤ l) (hkl : k = l) :
        Pi.π (fun i : ℕ ↦ X.obj (op i)) k ≫ X.map (homOfLE hk).op =
          Pi.π (fun i : ℕ ↦ X.obj (op i)) l ≫ X.map (homOfLE hl).op := by
      subst l
      rfl
    have h : s ≤ e * (n + 1 + 1) - 1 := by omega
    change Pi.π (fun i : ℕ ↦ X.obj (op i)) (e * (n + 1 + 1) - 1) ≫
        X.map (homOfLE h).op = _
    exact hcongr _ _ _ _ hnext.symm

private noncomputable def ordinaryCone
    {A : Type a} [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) : Cone I.asFunctor where
  pt := (limitComplex A).obj I
  π :=
    { app := fun n ↦
        { f := fun i ↦ limit.π (I.X i) n
          comm' := fun i j _ ↦ by
            exact (limMap_π (I.d i j) n).symm }
      naturality := fun m n f ↦ by
        ext i
        change 𝟙 _ ≫ limit.π (I.X i) n =
          limit.π (I.X i) m ≫ (I.X i).map f
        simp }

private noncomputable def familyMap
    {A : Type a} [Category.{b} A] [Abelian A]
    [HasCountableProducts A] [HasLimitsOfShape ℕᵒᵖ A]
    (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    (limitComplex A).obj I ⟶ ∏ᶜ (fun n : ℕ ↦ I.asFunctor.obj (op n)) :=
  Pi.lift (fun n ↦ (ordinaryCone I).π.app (op n))

open CochainComplex CochainComplex.HomComplex HomologicalComplex in
private lemma cocone_fst_f
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p : ℤ) :
    (mappingCocone.fst f).f p =
      ((mappingCone f).shiftFunctorObjXIso (-1) p (p - 1) (by omega)).hom ≫
        homotopyCofiber.fstX f (p - 1) p (by change p - 1 + 1 = p; omega) := by
  simp [mappingCocone.fst,
    Cochain.leftShift_v (n := 1) _ _ _ _ p p (add_zero p) (p - 1) (by omega),
    mappingCone.fst]

open CochainComplex CochainComplex.HomComplex HomologicalComplex in
private lemma cocone_snd_v
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p q : ℤ) (h : p + -1 = q) :
    (mappingCocone.snd f).v p q h =
      ((mappingCone f).shiftFunctorObjXIso (-1) p q (by omega)).hom ≫
        homotopyCofiber.sndX f q := by
  simp [mappingCocone.snd,
    Cochain.leftShift_v (n := 0) _ _ _ _ p q h q (add_zero q), mappingCone.snd,
    Int.negOnePow_even 2 ⟨1, rfl⟩]

open CochainComplex in
private noncomputable def coconeMap
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q P' Q' : CochainComplex A ℤ}
    (f : P ⟶ Q) (g : P' ⟶ Q') (a : P ⟶ P') (b : Q ⟶ Q')
    (h : f ≫ b = a ≫ g) : mappingCocone f ⟶ mappingCocone g :=
  (mappingCone.map f g a b h)⟦(-1 : ℤ)⟧'

private def ceilIndex (e : ℕ) : ℕᵒᵖ ⥤ ℕᵒᵖ :=
  (show ℕ →o ℕ from
    { toFun := fun n ↦ n / e
      monotone' := fun _ _ h ↦ Nat.div_le_div_right h }).monotone.functor.op
private lemma arithmetic_gc (e : ℕ) (he : 1 ≤ e) (i n : ℕ) :
    i / e ≤ n ↔ i ≤ e * (n + 1) - 1 := by
  have hp : 0 < e := he
  rw [Nat.div_le_iff_le_mul_add_pred hp]
  rw [Nat.mul_add, Nat.mul_one]
  omega
private def indexAdjunction (e : ℕ) (he : 1 ≤ e) : index e ⊣ ceilIndex e :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun n i ↦
        { toFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).2 f.unop.le)).op
          invFun := fun f ↦ (homOfLE ((arithmetic_gc e he i.unop n.unop).1 f.unop.le)).op
          left_inv := fun _ ↦ Subsingleton.elim _ _
          right_inv := fun _ ↦ Subsingleton.elim _ _ } }
private lemma limitMap_isIso
    (A : Type a) [Category.{b} A] [Abelian A] [HasLimitsOfShape ℕᵒᵖ A]
    (e : ℕ) (he : 1 ≤ e) (I : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    IsIso (limitMap e I) := by
  have : (index e).Initial := Functor.initial_of_adjunction (indexAdjunction e he)
  have (i : ℤ) : IsIso ((limitMap e I).f i) := by
    dsimp [limitMap]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma cocone_ext
    {A : Type a} [Category.{b} A] [Abelian A]
    {P Q K : CochainComplex A ℤ} (f : P ⟶ Q) (a b : K ⟶ CochainComplex.mappingCocone f)
    (hfst : a ≫ CochainComplex.mappingCocone.fst f =
      b ≫ CochainComplex.mappingCocone.fst f)
    (hsnd : ∀ (p q : ℤ) (h : p + -1 = q),
      a.f p ≫ (CochainComplex.mappingCocone.snd f).v p q h =
        b.f p ≫ (CochainComplex.mappingCocone.snd f).v p q h) : a = b := by
  apply HomologicalComplex.Hom.ext
  funext p
  have hf := congrArg (fun t ↦ t.f p) hfst
  change a.f p ≫ (CochainComplex.mappingCocone.fst f).f p =
    b.f p ≫ (CochainComplex.mappingCocone.fst f).f p at hf
  have hs := hsnd p (p - 1) (by omega)
  rw [cocone_fst_f] at hf
  rw [cocone_snd_v] at hs
  apply (cancel_mono ((CochainComplex.mappingCone f).shiftFunctorObjXIso
    (-1) p (p - 1) (by omega)).hom).mp
  apply HomologicalComplex.homotopyCofiber.ext_to_X f (p - 1) p (by
    change p - 1 + 1 = p; omega)
  · simpa only [Category.assoc] using hf
  · simpa only [Category.assoc] using hs

end CategoryTheory.StrictTowerArithmetic
