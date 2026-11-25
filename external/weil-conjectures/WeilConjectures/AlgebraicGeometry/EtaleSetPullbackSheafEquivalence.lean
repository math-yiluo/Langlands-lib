/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves

/-!
# Comparison of the set-valued inverse image with the inverse sheaf equivalence

Source: Stacks Project, Tags 04DZ and 03SI.
-/

set_option linter.style.haveILetI false
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tag 04DZ, inverse-image/topos equivalence.
Proof: The constructed set-valued inverse image is left adjoint to lowerStar.
The inverse of sheafEquivalence is also left adjoint to this same functor.
Adjunction.leftAdjointUniq gives the comparison isomorphism; take its inverse
for the displayed orientation.
(blueprint: thm-weil-pbc-etaleSetPullback_eq_sheafEquivalence) -/
theorem etaleSetPullback_eq_sheafEquivalence {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    Nonempty ((sheafEquivalence (Type (u + 1)) u).symm.functor ≅
      Scheme.etaleSetPullback u) := by
  exact ⟨((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
    u.Etale (Type (u + 1)) X.smallEtaleTopology X'.smallEtaleTopology).leftAdjointUniq
    (sheafEquivalence (Type (u + 1)) u).symm.toAdjunction).symm⟩
end AlgebraicGeometry.Etale
