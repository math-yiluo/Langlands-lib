/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.TopologicalInvariance
public import WeilConjectures.AlgebraicGeometry.EtaleSheaves
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# Universal-homeomorphism identity coherence

Source: Stacks Project, Tags 04DZ and 03SI.
-/

set_option linter.style.haveILetI false
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tags 04DZ and 03SI, identity coherence.
Proof: For the identity scheme morphism, lowerStarId identifies the set-valued pushforward with the
identity functor. Transport the sheaf pullback adjunction along this isomorphism and compare it
with the identity adjunction by leftAdjointUniq. This gives the set-valued inverse-image identity
isomorphism. Equivalently, the repaired comparison identifies it with the inverse sheaf
equivalence, whose adjunction is compared to the same identity adjunction.
Use lowerStarId with Type coefficients for the second isomorphism, upperStarId with additive
coefficients for the third, and lowerStarId with additive coefficients for the fourth. The
identity clause of cohomologyPullbackFunctorial gives exactly the displayed equality for every F,
q and x.
(blueprint: thm-weil-pbc-universalHomeomorphism_identity) -/
theorem universalHomeomorphism_identity {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    Nonempty (Scheme.etaleSetPullback (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (lowerStar (Type (u + 1)) (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (𝟙 X) ≅ 𝟭 _) ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} (𝟙 X) ≅ 𝟭 _) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map ((upperStarId AddCommGrpCat.{u + 1} X).hom.app F) q
          (cohomologyMap (𝟙 X) F q x) = x := by
  refine ⟨?_, ⟨lowerStarId (Type (u + 1)) X⟩,
    ⟨upperStarId AddCommGrpCat.{u + 1} X⟩,
    ⟨lowerStarId AddCommGrpCat.{u + 1} X⟩, ?_⟩
  · exact ⟨(Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
      ((𝟙 X) : X ⟶ X).Etale (Type (u + 1)) X.smallEtaleTopology
        X.smallEtaleTopology).leftAdjointIdIso
        (lowerStarId (Type (u + 1)) X)⟩
  · intro F q x
    exact (cohomologyPullbackFunctorial (𝟙 X) (𝟙 X) F q).2.2 x
end AlgebraicGeometry.Etale
