/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Direct.DirectImageScalarOperations
import WeilConjectures.AlgebraicGeometry.ProEtale.Canonical.ProEtaleCanonicalDerivedPullbackNormalization
import WeilConjectures.AlgebraicGeometry.DirectScalar.ConstantScalarPullbackSquare
import WeilConjectures.AlgebraicGeometry.StrictTower.FiniteOpenBaseChangeNormalized
import WeilConjectures.CategoryTheory.DerivedCategory.MapDerivedCategoryMate

/-!
# The coefficient cube for canonical constant-ring inverse images

## References

* Stacks Project, Tags 0D6D and 0E47, coefficient inverse-image comparisons
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false


@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
-- Replaying the dependent transport calculations for tactic linting is expensive.
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

open AlgebraicGeometry.ProEtale
attribute [local irreducible] completedAdicDerivedChange
  Functor.mapDerivedCategory Functor.rightDerivedFunctor proEtaleCanonicalDerivedPullbackComparison
  proEtaleRingCompositeCoefficients

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem derived_transport
    {T V : Scheme.{u}} {f g : T ⟶ V} (e : f = g) (A : Type u) [CommRing A] :
    (Functor.mapDerivedCategoryNatIso
      (eqToIso (congrArg (StrictTower.modulePullback (ULift.{u + 1, u} A)) e))).hom =
      (eqToIso (congrArg (proEtaleConstantRingDerivedPullback A) e)).hom := by
  cases e
  exact Functor.mapDerivedCategoryNatIso_refl

end AlgebraicGeometry.Scheme
