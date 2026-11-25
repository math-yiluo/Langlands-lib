/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import WeilConjectures.CategoryTheory.Limits.TowerTransitionEndomorphism
import WeilConjectures.Algebra.Homology.KernelShiftedMappingCone

/-! # Roos comparison for complexes with split transitions

Source: Stacks Project, Derived Categories, Tag 070M, and the split-envelope
extension recorded in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-split-comparison).
-/

@[expose] public section

universe u v

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

private theorem transition_isSplitEpi
    {A : Type u} [Category.{v} A] [Preadditive A]
    {K : ℕ → A} [HasProduct K] (f : ∀ n, K (n + 1) ⟶ K n)
    (hf : ∀ n, IsSplitEpi (f n)) : IsSplitEpi (towerTransitionEndomorphism f) := by
  classical
  let a : ∀ n, ∏ᶜ K ⟶ K n := fun n ↦ Nat.rec (0 : ∏ᶜ K ⟶ K 0)
    (fun n an ↦ (an - Limits.Pi.π K n) ≫ @section_ _ _ _ _ (f n) (hf n)) n
  have ha (n : ℕ) : a (n + 1) ≫ f n = a n - Limits.Pi.π K n := by
    dsimp [a]
    simp only [Category.assoc, IsSplitEpi.id, Category.comp_id]
  refine IsSplitEpi.mk' ⟨Limits.Pi.lift a, ?_⟩
  apply Limits.Pi.hom_ext
  intro n
  simp only [towerTransitionEndomorphism, towerProductShift, Preadditive.comp_sub,
    Category.comp_id, Preadditive.sub_comp, Category.assoc,
    Limits.Pi.lift_comp_π, Category.id_comp]
  rw [Limits.Pi.lift_comp_π_assoc, ha]
  simp

private noncomputable abbrev towerProductComplex
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A] (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    CochainComplex A ℤ where
  X p := ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n))
  d p q := Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n))
  shape p q h := by
    rw [J.shape p q h]
    apply Limits.Pi.hom_ext
    intro n
    simp
  d_comp_d' p q r _ _ := by
    apply Limits.Pi.hom_ext
    intro n
    simp only [Category.assoc, Limits.Pi.map_π, Limits.Pi.map_π_assoc]
    rw [← NatTrans.comp_app, J.d_comp_d]
    simp

private noncomputable abbrev towerProductTransition
    {A : Type u} [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A] (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ) :
    towerProductComplex J ⟶ towerProductComplex J where
  f p := towerTransitionEndomorphism
    (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op)
  comm' p q _ := by
    dsimp [towerProductComplex]
    symm
    apply towerTransitionEndomorphism_natural_backward
    intro n
    exact ((J.d p q).naturality (homOfLE (Nat.le_succ n)).op).symm

@[reassoc]
private theorem cofiber_biprod_snd
    {A : Type u} [Category.{v} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p q : ℤ)
    (h : (ComplexShape.up ℤ).Rel p q) :
    (HomologicalComplex.homotopyCofiber.XIsoBiprod f p q h).hom ≫
      biprod.snd = HomologicalComplex.homotopyCofiber.sndX f p := by
  obtain rfl := (ComplexShape.up ℤ).next_eq' h
  dsimp only [HomologicalComplex.homotopyCofiber.sndX]
  rw [dite_eq_left h]

@[reassoc]
private theorem cofiber_biprod_fst
    {A : Type u} [Category.{v} A] [Abelian A]
    {P Q : CochainComplex A ℤ} (f : P ⟶ Q) (p q : ℤ)
    (h : (ComplexShape.up ℤ).Rel p q) :
    (HomologicalComplex.homotopyCofiber.XIsoBiprod f p q h).hom ≫
      biprod.fst = HomologicalComplex.homotopyCofiber.fstX f p q h := rfl

set_option backward.isDefEq.respectTransparency false in
/-- A split-term complex has a product/kernel/signed-cone presentation whose
canonical comparison is a quasi-isomorphism. This is the split case, with no
K-injectivity hypothesis.

Proof: Form PJ termwise by countable products and let sJ be one minus transition
shift. Naturality of the transition shift gives a chain map. Define LJ as its
kernel complex. Take CJ to be the Mathlib mapping cone of sJ shifted by -1.
Compose its degree isomorphism with the biproduct swap to identify its terms
with PJ^(p-1) ⊞ PJ^p. The shift changes the sign of the cone differential,
and its two projection equations give (y,x) ↦ (-dy-sJ x, dx).
Choose a section σ_n of each split transition in every degree. On the product
recursively define a_n by a_0=0 and a_(n+1)=(a_n-pr_n)σ_n. Their product lift a
satisfies a sJ = id by checking every projection, so sJ is degreewise epi.
Apply the degreewise-epi kernel/shifted-cone comparison. Its projection
equations, reindexed in degree p+1 and composed with the biproduct swap,
identify it with (0,iJ). It is already a quasi-isomorphism into CJ. Evaluation
functors preserve kernels, giving the required limiting kernel forks.

Source: Stacks Project, Derived Categories, Tag 070M; the explicit extension
in lem-weil-derived-limit-roos-complex.
(blueprint: lem-weil-roos-split-comparison). -/
theorem roos_split_comparison
    (A : Type u) [Category.{v} A] [Abelian A]
    [HasLimitsOfShape (Discrete ℕ) A]
    (J : CochainComplex (ℕᵒᵖ ⥤ A) ℤ)
    (hSplit : ∀ (p : ℤ) (n : ℕ),
      IsSplitEpi ((J.X p).map (homOfLE (Nat.le_succ n)).op)) :
    ∃ (PJ LJ CJ : CochainComplex A ℤ)
      (ePJ : ∀ p : ℤ, PJ.X p ≅ ∏ᶜ (fun n : ℕ ↦ (J.X p).obj (Opposite.op n)))
      (sJ : PJ ⟶ PJ) (iJ : LJ ⟶ PJ)
      (hKJ : ∀ p : ℤ, iJ.f p ≫ sJ.f p = 0)
      (eCJ : ∀ p : ℤ, CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1))
      (etaJ : LJ ⟶ CJ)
      (_hLJ : ∀ p : ℤ, IsLimit (KernelFork.ofι (iJ.f p) (hKJ p))),
      (∀ p q : ℤ, PJ.d p q ≫ (ePJ q).hom =
      (ePJ p).hom ≫ Limits.Pi.map (fun n ↦ (J.d p q).app (Opposite.op n))) ∧
      (∀ p : ℤ, sJ.f p = (ePJ p).hom ≫
      towerTransitionEndomorphism
        (fun n ↦ (J.X p).map (homOfLE (Nat.le_succ n)).op) ≫ (ePJ p).inv) ∧
      (∀ p : ℤ, CJ.d (p + 1) (p + 1 + 1) ≫ (eCJ (p + 1)).hom =
      (eCJ p).hom ≫ biprod.lift
        (-(biprod.fst ≫ PJ.d p (p + 1)) - biprod.snd ≫ sJ.f (p + 1))
        (biprod.snd ≫ PJ.d (p + 1) (p + 1 + 1))) ∧
      (∀ p : ℤ, etaJ.f (p + 1) ≫ (eCJ p).hom = biprod.lift 0 (iJ.f (p + 1))) ∧
      QuasiIso etaJ := by
  classical
  let PJ := towerProductComplex J
  let sJ := towerProductTransition J
  have hs (p : ℤ) : Epi (sJ.f p) := by
    have : IsSplitEpi (sJ.f p) := transition_isSplitEpi _ (hSplit p)
    infer_instance
  let _ := HasDerivedCategory.standard A
  obtain ⟨κ, hκ, hqκ, _⟩ :=
    CochainComplex.exists_kernel_to_shifted_mappingCone_of_degreewise_epi sJ hs
  let CJ := (CochainComplex.mappingCone sJ)⟦(-1 : ℤ)⟧
  let eS (p : ℤ) := (CochainComplex.mappingCone sJ).shiftFunctorObjXIso
    (-1) (p + 1) p (by omega)
  let eB (p : ℤ) := HomologicalComplex.homotopyCofiber.XIsoBiprod sJ p (p + 1) rfl
  let eC (p : ℤ) : CJ.X (p + 1) ≅ PJ.X p ⊞ PJ.X (p + 1) :=
    eS p ≪≫ eB p ≪≫ biprod.braiding _ _
  have hK (p : ℤ) : (kernel.ι sJ).f p ≫ sJ.f p = 0 := by
    exact congrArg (fun f ↦ f.f p) (kernel.condition sJ)
  have hL (p : ℤ) : IsLimit (KernelFork.ofι ((kernel.ι sJ).f p) (hK p)) :=
    isLimitOfHasKernelOfPreservesLimit (HomologicalComplex.eval A (ComplexShape.up ℤ) p) sJ
  refine ⟨PJ, kernel sJ, CJ, fun _ ↦ Iso.refl _, sJ, kernel.ι sJ, hK, eC,
    κ, hL, ?_, ?_, ?_, ?_, hqκ⟩
  · intro p q
    simp [PJ, towerProductComplex]
  · intro p
    simp only [Iso.refl_hom, Iso.refl_inv, Category.id_comp]
    rw [Category.comp_id]
  · intro p
    have hd : CJ.d (p + 1) (p + 1 + 1) ≫ (eS (p + 1)).hom =
        -(eS p).hom ≫ (CochainComplex.mappingCone sJ).d p (p + 1) := by
      dsimp only [CJ, eS, CochainComplex.shiftFunctorObjXIso]
      simp only [CochainComplex.shiftFunctor_obj_d', Int.negOnePow_neg,
        Int.negOnePow_one, Units.neg_smul, one_smul, Preadditive.neg_comp,
        HomologicalComplex.d_comp_XIsoOfEq_hom,
        HomologicalComplex.XIsoOfEq_hom_comp_d]
    dsimp only [eC, Iso.trans_hom]
    rw [← Category.assoc, hd]
    apply biprod.hom_ext
    · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_fst,
        Preadditive.neg_comp, Preadditive.comp_sub, Preadditive.comp_neg]
      rw [biprod.lift_fst, biprod.lift_fst_assoc, biprod.lift_snd_assoc]
      dsimp only [eB]
      rw [cofiber_biprod_snd, cofiber_biprod_snd_assoc, cofiber_biprod_fst_assoc]
      change -(eS p).hom ≫ HomologicalComplex.homotopyCofiber.d sJ p (p + 1) ≫
          HomologicalComplex.homotopyCofiber.sndX sJ (p + 1) =
        -(eS p).hom ≫ HomologicalComplex.homotopyCofiber.sndX sJ p ≫
          PJ.d p (p + 1) -
        (eS p).hom ≫ HomologicalComplex.homotopyCofiber.fstX sJ p (p + 1) rfl ≫
          sJ.f (p + 1)
      rw [HomologicalComplex.homotopyCofiber.d_sndX sJ p (p + 1) rfl]
      simp only [Preadditive.comp_add]
      abel
    · simp only [Category.assoc, biprod.braiding_hom, biprod.lift_snd,
        Preadditive.neg_comp]
      rw [biprod.lift_snd, biprod.lift_snd_assoc]
      dsimp only [eB]
      rw [cofiber_biprod_fst, cofiber_biprod_fst_assoc]
      change -(eS p).hom ≫ HomologicalComplex.homotopyCofiber.d sJ p (p + 1) ≫
          HomologicalComplex.homotopyCofiber.fstX sJ (p + 1) (p + 1 + 1) rfl =
        (eS p).hom ≫ HomologicalComplex.homotopyCofiber.fstX sJ p (p + 1) rfl ≫
          PJ.d (p + 1) (p + 1 + 1)
      rw [HomologicalComplex.homotopyCofiber.d_fstX sJ p (p + 1) (p + 1 + 1) rfl rfl]
      simp only [Preadditive.comp_neg, neg_neg]
      rfl
  · intro p
    have hk' (r q : ℤ) (h : q = r - 1) :
        κ.f r ≫ ((CochainComplex.mappingCone sJ).shiftFunctorObjXIso
          (-1) r q (by omega)).hom ≫
            HomologicalComplex.homotopyCofiber.sndX sJ q = 0 ∧
        κ.f r ≫ ((CochainComplex.mappingCone sJ).shiftFunctorObjXIso
          (-1) r q (by omega)).hom ≫
            HomologicalComplex.homotopyCofiber.fstX sJ q r
              (by change q + 1 = r; omega) = (kernel.ι sJ).f r := by
      subst q
      exact hκ r
    have hk₁ := (hk' (p + 1) p (by omega)).1
    have hk₂ := (hk' (p + 1) p (by omega)).2
    apply biprod.hom_ext
    · simp only [eC, Iso.trans_hom, Category.assoc, biprod.braiding_hom,
        biprod.lift_fst]
      rw [biprod.lift_fst]
      dsimp only [eB]
      rw [cofiber_biprod_snd]
      exact hk₁
    · simp only [eC, Iso.trans_hom, Category.assoc, biprod.braiding_hom,
        biprod.lift_snd]
      rw [biprod.lift_snd]
      exact hk₂

end CategoryTheory
