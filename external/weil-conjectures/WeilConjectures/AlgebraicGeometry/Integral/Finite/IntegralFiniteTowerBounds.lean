/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.AdicCompletion.DerivedCompletionSupplement
public import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.Triangulated.DerivedLimitProducts
import WeilConjectures.CategoryTheory.ModuleObjects.SequentialLimitEpi
import WeilConjectures.AlgebraicGeometry.ProEtale.RepleteAddCommGrp
import WeilConjectures.Algebra.Homology.DerivedCategory.Ext.TowerLimit

/-! # The cohomological range of a complete integral reduction tower
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

private theorem limitTriangle_bounds
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [HasCountableProducts C] [CountableAB4Star C] [HasLimitsOfShape ℕᵒᵖ C]
    (hrep : EpiπAppZeroOfEpi C)
    (L : ℕ → DerivedCategory C) (t : ∀ n, L (n + 1) ⟶ L n)
    [HasProduct L] (K : DerivedCategory C)
    (p : K ⟶ ∏ᶜ L) (δ : ∏ᶜ L ⟶ K⟦(1 : ℤ)⟧)
    (hT : IsDerivedLimitTriangle t K p δ) (a b : ℤ)
    (hL : ∀ n, DerivedCategory.homologyConcentratedIn a b (L n))
    (ht : ∀ n, Epi ((DerivedCategory.homologyFunctor C b).map (t n))) :
    DerivedCategory.homologyConcentratedIn a b K := by
  classical
  have hH (q : ℤ) : PreservesLimitsOfShape (Discrete ℕ)
      (DerivedCategory.homologyFunctor C q) :=
    (derivedCategory_countableProducts_core C).choose_spec.2 ℕ q
  have hzero (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor C q).obj (∏ᶜ L)) := by
    have := hH q
    apply (isLimitOfHasProductOfPreservesLimit
      (DerivedCategory.homologyFunctor C q) L).isZero_pt
    apply Functor.isZero
    intro n
    rcases hq with hq | hq
    · exact DerivedCategory.isZero_of_isGE _ a q hq (hX := (hL n.as).1)
    · exact DerivedCategory.isZero_of_isLE _ b q hq (hX := (hL n.as).2)
  let H := DerivedCategory.homologyFunctor C b
  have := hH b
  let F := Functor.ofOpSequence (X := fun n ↦ H.obj (L n)) (fun n ↦ H.map (t n))
  let P : Fan (fun n : ℕ ↦ F.obj (Opposite.op n)) :=
    Fan.mk (H.obj (∏ᶜ L)) (fun n ↦ H.map (Pi.π L n))
  have hP : IsLimit P := isLimitOfHasProductOfPreservesLimit H L
  have htop : Epi (H.map (towerTransitionEndomorphism t)) := by
    rw [towerTransitionEndomorphism, H.map_sub, H.map_id]
    apply epi_one_sub_of_epiπAppZeroOfEpi hrep (F := F)
      (fun n ↦ by simpa [F] using ht n) hP
    intro n
    change H.map (towerProductShift t) ≫ H.map (Pi.π L n) =
      H.map (Pi.π L (n + 1)) ≫ F.map (homOfLE n.le_succ).op
    rw [show F.map (homOfLE n.le_succ).op = H.map (t n) from
      Functor.ofOpSequence_map_homOfLE_succ _ n]
    rw [← H.map_comp, ← H.map_comp]
    congr 1
    simp [towerProductShift]
  let T := CategoryTheory.Pretriangulated.Triangle.mk p
    (towerTransitionEndomorphism t) δ
  change T ∈ distTriang _ at hT
  have hz (q : ℤ) (hq : q < a ∨ b < q) :
      IsZero ((DerivedCategory.homologyFunctor C q).obj K) := by
    by_cases hqtop : q = b + 1
    · subst q
      have hd := DerivedCategory.HomologySequence.comp_δ T hT b (b + 1) rfl
      have : Epi ((DerivedCategory.homologyFunctor C b).map T.mor₂) := htop
      have hex := DerivedCategory.HomologySequence.exact₁ T hT b (b + 1) rfl
      apply hex.isZero_of_both_zeros
      · exact (cancel_epi ((DerivedCategory.homologyFunctor C b).map T.mor₂)).mp
          (by simpa using hd)
      · exact (hzero (b + 1) hq).eq_zero_of_tgt _
    · have hex := DerivedCategory.HomologySequence.exact₁ T hT (q - 1) q (by omega)
      exact hex.isZero_of_both_isZero (hzero (q - 1) (by omega)) (hzero q hq)
  exact ⟨(DerivedCategory.isGE_iff K a).mpr (fun q hq ↦ hz q (Or.inl hq)),
    (DerivedCategory.isLE_iff K b).mpr (fun q hq ↦ hz q (Or.inr hq))⟩

/-- The common cohomological range of the canonical reductions bounds a complete complex
when the top cohomology transitions are epic. -/
theorem integral_finite_tower_bounds
    (l : ℕ) [Fact l.Prime] (E : Type u) [Field E]
    [Algebra (Padic l) E] [FiniteDimensional (Padic l) E]
    (X : Scheme.{u}) (K : DerivedCategory (AdicCompletion.Modules l E X))
    (hcomplete : IsDerivedComplete l E X K) (a b : ℤ)
    (hlevel : ∀ n, DerivedCategory.homologyConcentratedIn a b
      (AdicCompletion.integralLevel l E X K n))
    (htop : ∀ n, Epi ((DerivedCategory.homologyFunctor
      (AdicCompletion.Modules l E X) b).map (AdicCompletion.integralStep l E X K n))) :
    DerivedCategory.homologyConcentratedIn a b K := by
  classical
  let C := AdicCompletion.Modules l E X
  have hrep : EpiπAppZeroOfEpi C :=
    Mod.epiπAppZeroOfEpi Scheme.ProEt.epi_π_app_zero_of_epi_addCommGrpCat
  let : CountableAB4Star C := .of_epi_π_app_zero hrep
  let := (derivedCategory_countableProducts_core.{0} C).choose
  obtain ⟨P, hP, ⟨e⟩, hη⟩ := hcomplete
  obtain ⟨p, δ, hT, _⟩ := AdicCompletion.roos_isDerivedLimit l E X K P hP e
  have hrange := limitTriangle_bounds hrep (AdicCompletion.integralLevel l E X K)
    (AdicCompletion.integralStep l E X K) _ p δ hT a b hlevel htop
  let : IsIso (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P)) := hη
  let ecomplete := e.symm ≪≫ asIso
    (DerivedCategory.Q.map (AdicCompletion.augmentation l E X P))
  exact (DerivedCategory.homologyConcentratedIn a b).prop_of_iso ecomplete.symm hrange

end AlgebraicGeometry.ProEtale
