/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtalePairFlasque
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
import Mathlib.Algebra.Homology.HomologicalComplexAbelian
import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
import WeilConjectures.CategoryTheory.Sites.InjectiveSheafSmulEpi
import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.LowerShriek.Open.Defs

/-!
# Exact sequence of supported sections for injective pro-etale complexes

## References

* Stacks Project, Tags 03EJ, 03EI, 09AH and 0114
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Scheme

namespace ProEtale

/-- Apply the actual closed supported inverse image and direct image term by term. -/
noncomputable def supportedSectionsComplex
    (R : Type (u + 1)) [CommRing R] [Finite R] {Z U X : Scheme.{u}}
    (s : Z ⟶ X) (j : U ⟶ X)
    [IsClosedImmersion s] [IsOpenImmersion j]
    (hcompl : IsCompl (Set.range s.base) (Set.range j.base))
    (I : CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ) :
    CochainComplex (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} R)) ℤ :=
  letI : PreservesFiniteLimits (finiteClosedUpperShriek R s j) :=
    (finiteSupportedSections_leftExact R s j hcompl).2
  (((s)_*[ModuleCat.{u + 1} R]).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (((finiteClosedUpperShriek R s j).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I)

end AlgebraicGeometry.ProEtale
