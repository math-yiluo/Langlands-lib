/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import WeilConjectures.AlgebraicGeometry.Cohomology.Affine.CechAcyclic
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! # Global lifting in an affine extension

## References

* Stacks Project, Schemes, Lemma 01IE, ideal and principal-open lifting argument
* Stacks Project, Schemes, from "Pick m" to the end of its proof
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Scheme.Modules

/-- The quotient map of an affine extension with quasi-coherent ends is surjective on
 global sections.
-/
theorem epi_globalSections_of_shortExact {R : CommRingCat.{u}}
    (S : ShortComplex (Spec R).Modules) (hS : S.ShortExact)
    [S.X₁.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    Epi ((moduleSpecΓFunctor (R := R)).map S.g) := by
  -- Use the proved Čech lifting criterion instead of the ideal argument above.
  let F := SheafOfModules.toSheaf.{u} (Spec R).ringCatSheaf
  have : F.Additive := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteLimits F := inferInstance
  have : CategoryTheory.Limits.PreservesFiniteColimits F := inferInstance
  apply (ModuleCat.epi_iff_surjective _).mpr
  exact surjective_app_of_cechAcyclicOnAffines (hS.map_of_exact F)
    (cechAcyclicOnAffines_of_isQuasicoherent S.X₁) (isAffineOpen_top (Spec R))

end AlgebraicGeometry.Scheme.Modules
