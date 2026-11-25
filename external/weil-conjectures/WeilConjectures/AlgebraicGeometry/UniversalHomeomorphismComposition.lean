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
# Universal-homeomorphism composition coherence

Source: Stacks Project, Tags 04DZ and 03SI.
-/

set_option linter.style.haveILetI false
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale

/-- Source: Stacks Project, Tags 04DZ and 03SI, composition coherence.
Proof: Compose the set-valued sheaf pullback adjunctions for u and v. lowerStarComp identifies their
composite right adjoint with the right adjoint for v ≫ u. Transport the composite adjunction along
this isomorphism and compare the left adjoints using leftAdjointUniq, then invert to obtain the
displayed set-valued compositor. The repaired comparison with inverse sheaf equivalences permits
the same construction through the equivalences for u, v and v ≫ u; it provides natural
isomorphisms, never equalities.
Use lowerStarComp for the Type-valued and additive pushforward compositors and upperStarComp for
the additive inverse-image compositor. The composition clause of cohomologyPullbackFunctorial
expresses successive pullback as Sheaf.H.map of the forward compositor applied to pullback along v
≫ u. Apply Sheaf.H.map of the inverse compositor; functoriality of Sheaf.H.map and the inverse-hom
identity cancel these maps and give the displayed equality.
(blueprint: thm-weil-pbc-universalHomeomorphism_composition) -/
theorem universalHomeomorphism_composition {X X' : Scheme.{u}} (u : X' ⟶ X)
    [IsUniversalHomeomorphism u] :
    ∀ (X'' : Scheme.{u}) (v : X'' ⟶ X'), IsUniversalHomeomorphism v →
      Nonempty (Scheme.etaleSetPullback (v ≫ u) ≅
        Scheme.etaleSetPullback u ⋙ Scheme.etaleSetPullback v) ∧
      Nonempty (lowerStar (Type (u + 1)) (v ≫ u) ≅
        lowerStar (Type (u + 1)) v ⋙ lowerStar (Type (u + 1)) u) ∧
      Nonempty (upperStar AddCommGrpCat.{u + 1} (v ≫ u) ≅
        upperStar AddCommGrpCat.{u + 1} u ⋙ upperStar AddCommGrpCat.{u + 1} v) ∧
      Nonempty (lowerStar AddCommGrpCat.{u + 1} (v ≫ u) ≅
        lowerStar AddCommGrpCat.{u + 1} v ⋙ lowerStar AddCommGrpCat.{u + 1} u) ∧
      ∀ (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)
        (x : Sheaf.H F q),
        Sheaf.H.map ((upperStarComp AddCommGrpCat.{u + 1} v u).inv.app F) q
          (cohomologyMap v ((upperStar AddCommGrpCat.{u + 1} u).obj F) q
            (cohomologyMap u F q x)) = cohomologyMap (v ≫ u) F q x := by
  intro X'' v hv
  refine ⟨?_, ⟨(lowerStarComp (Type (u + 1)) v u).symm⟩,
    ⟨upperStarComp AddCommGrpCat.{u + 1} v u⟩,
    ⟨(lowerStarComp AddCommGrpCat.{u + 1} v u).symm⟩, ?_⟩
  · exact ⟨(Adjunction.leftAdjointCompIso
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        u.Etale (Type (u + 1)) X.smallEtaleTopology X'.smallEtaleTopology)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        v.Etale (Type (u + 1)) X'.smallEtaleTopology X''.smallEtaleTopology)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous
        (v ≫ u).Etale (Type (u + 1)) X.smallEtaleTopology X''.smallEtaleTopology)
      (lowerStarComp (Type (u + 1)) v u)).symm⟩
  · intro F q x
    rw [(cohomologyPullbackFunctorial v u F q).2.1 x]
    rw [← Sheaf.H.map_comp_apply]
    simp only [Iso.hom_inv_id_app, Sheaf.H.map_id_apply]
end AlgebraicGeometry.Etale
