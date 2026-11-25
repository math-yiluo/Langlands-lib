/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import WeilConjectures.Algebra.Homology.IdealPowerTorsionCocomplexInclusion
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedFlasqueResolutionCohomology
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedSectionsTorsionQuotient

/-! # Computing puncture cohomology by the quotient of an injective resolution

## References

* Stacks Project, Tag 0BK0, Lemma 51.8.2
* Tag 0A6T, Lemma 51.2.1
* Stacks Project, Tag 09T2
-/

@[expose] public section

universe u
open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

/-- The quotient of a module injective resolution by its maximal-ideal-power torsion
subcomplex computes cohomology on the puncture, in every degree.
-/
theorem nonempty_punctured_h_addEquiv_injective_quotient
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (I : InjectiveResolution (ModuleCat.of R R : ModuleCat.{u} R)) (n : ℕ) :
    Nonempty (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) n ≃+
      ((cokernel (ModuleCat.idealPowerTorsionCocomplexι
        (IsLocalRing.maximalIdeal R) I.cocomplex)).homology n).carrier) := by
  obtain ⟨e⟩ := nonempty_open_h_addEquiv_injective_sections R W I n
  obtain ⟨q⟩ := nonempty_injective_quotient_iso_punctured_sections R W hW I
  let h := (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) n).mapIso q
  exact ⟨e.trans h.symm.toLinearEquiv.toAddEquiv⟩

end AlgebraicGeometry.Scheme
