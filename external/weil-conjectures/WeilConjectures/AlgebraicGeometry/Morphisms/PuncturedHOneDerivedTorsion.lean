/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionFunctor
public import Mathlib.Algebra.Category.ModuleCat.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.RightDerived
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedInjectiveQuotientCohomology
import Mathlib.Algebra.Homology.HomologySequence

/-! # The puncture localization sequence for derived torsion

## References

* Stacks Project, Tags 0BK0, 0A6T, and 09T2
* Stacks Project, Tag 0BK0, Lemma 51.8.2(2), and Tag 0A6T, Lemma 51.2.1
-/

@[expose] public section

universe u
open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- The localization boundary identifies H¹ of the puncture with derived torsion in degree two.
The flasqueness input is Tag 09T2, Lemma 36.8.1. -/
theorem nonempty_punctured_h_one_addEquiv_derived_torsion
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R) :
    Nonempty (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1 ≃+
      (((ModuleCat.idealPowerTorsion (IsLocalRing.maximalIdeal R)).rightDerived 2).obj
        (ModuleCat.of R R : ModuleCat.{u} R)).carrier) := by
  classical
  obtain ⟨I⟩ := HasInjectiveResolution.out (Z := (ModuleCat.of R R : ModuleCat.{u} R))
  let f := ModuleCat.idealPowerTorsionCocomplexι (IsLocalRing.maximalIdeal R) I.cocomplex
  let S := ShortComplex.cokernelSequence f
  have hS : S.ShortExact :=
    ShortComplex.ShortExact.mk' (ShortComplex.cokernelSequence_exact f)
      (inferInstance : Mono f) inferInstance
  have h₁ : CategoryTheory.Limits.IsZero (I.cocomplex.homology 1) :=
    (I.cocomplex_exactAt_succ 0).isZero_homology
  have h₂ : CategoryTheory.Limits.IsZero (I.cocomplex.homology 2) :=
    (I.cocomplex_exactAt_succ 1).isZero_homology
  obtain ⟨e⟩ := nonempty_punctured_h_addEquiv_injective_quotient R W hW I 1
  let δ := hS.δIso 1 2 (by decide) h₁ h₂
  let d := I.isoRightDerivedObj (ModuleCat.idealPowerTorsion (IsLocalRing.maximalIdeal R)) 2
  exact ⟨e.trans (δ.toLinearEquiv.toAddEquiv.trans d.symm.toLinearEquiv.toAddEquiv)⟩

end AlgebraicGeometry.Scheme
