/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
public import WeilConjectures.SixFunctors.BaseChange.Etale
public import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportFiniteGraphIso
import WeilConjectures.AlgebraicGeometry.Etale.Compact.EtaleCompactSupportNormalizationDataSupplement
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphSheafNormalization
import WeilConjectures.SixFunctors.BaseChange.Etale
import WeilConjectures.ConstructibleSheaf.EtaleMorphismDescent
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.FullyFaithful
import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphGeometricBaseChange
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.OpenImmersionLowerShriekProjectionBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.EtaleLowerShriekBaseChange
import WeilConjectures.SixFunctors.Etale.Derived.BaseChangeCube
import WeilConjectures.SixFunctors.Etale.Derived.UpperStarIdCoherence
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.Local
import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStar
import WeilConjectures.SixFunctors.OpenClosed.Conservative
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import WeilConjectures.AlgebraicGeometry.EtaleCompactSupportGraphDerivedIso

/-!
# Invertibility of the graph comparison on unbounded complexes

Source: SGA 4 XVII 5.2.2 and 6.2.11; Stacks Project Tags 03S6 and 0F0C
(blueprint: lem-asd-compact-support-graph-derived-isomorphism).
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/-- Core data from the specified graph map, with its forced inverse and termwise descent.
Source: SGA 4 XVII 6.2.11
(blueprint: lem-asd-compact-support-graph-derived-isomorphism). -/
noncomputable def canonicalEtaleCompactSupportCore
    (A : Type (u + 1)) [CommRing A] [Finite A] : EtaleCompactSupportCore A where
  comparison := fun f _ _ _ _ _ _ c ↦ canonicalEtaleCompactSupportComparison A f c
  sheafComparison := fun f _ _ _ _ _ _ c => etaleCompactificationGraphMap A f c
  sheaf_normalization := fun f _ _ _ _ _ _ c M =>
    compactSupportGraphSheafComparison_normalization A f c M
  derived_normalization := by
    intro U X f hf hs hU hUc hX hXc c K
    exact compactSupportDerivedComparison_app A f c (etaleCompactificationGraphMap A f c) K

end AlgebraicGeometry.Etale
