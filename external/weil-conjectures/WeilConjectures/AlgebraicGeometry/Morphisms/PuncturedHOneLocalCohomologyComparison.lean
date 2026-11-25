/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.Defs
public import Mathlib.Algebra.Homology.LocalCohomology
import WeilConjectures.Algebra.Homology.LocalCohomologyDerivedTorsion
import WeilConjectures.AlgebraicGeometry.Morphisms.PuncturedHOneDerivedTorsion

/-! # PuncturedHOneLocalCohomologyComparison

## References

* Stacks Project, Tag 0BK0, Lemma 51.8.2(2), Tag 0A6T, Lemma 51.2.1, and Tag 0AVY, Lemma 47.11.1
  (the Ext-colimit description)
-/

@[expose] public section

universe u
namespace AlgebraicGeometry.Scheme

/-- Comparison from punctured-spectrum cohomology to local cohomology. -/
theorem punctured_h_one_subsingleton_of_local_cohomology_vanishing
    (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    (W : (Spec (.of R)).Opens)
    (hW : ∀ x : Spec (.of R), x ∈ W ↔ x ≠ IsLocalRing.closedPoint R)
    (hzero : Subsingleton ((localCohomology (IsLocalRing.maximalIdeal R) 2).obj
      ((ModuleCat.of R R : ModuleCat.{u} R))).carrier) :
    Subsingleton (Modules.H (X := W.toScheme)
      (SheafOfModules.unit W.toScheme.ringCatSheaf) 1) := by
  obtain ⟨e⟩ := ModuleCat.nonempty_localCohomology_iso_derived_torsion
    (IsLocalRing.maximalIdeal R) (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
    (ModuleCat.of R R : ModuleCat.{u} R) 2
  obtain ⟨d⟩ := nonempty_punctured_h_one_addEquiv_derived_torsion R W hW
  refine ⟨fun x y ↦ d.injective ?_⟩
  apply e.toLinearEquiv.symm.injective
  exact hzero.elim _ _

end AlgebraicGeometry.Scheme
