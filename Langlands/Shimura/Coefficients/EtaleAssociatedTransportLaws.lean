import Langlands.Shimura.Coefficients.EtaleAssociatedTransport

/-! # Transport maps along the identity and twisted transport data

Two laws for the transport maps of `Langlands.Shimura.Coefficients.EtaleAssociatedTransport`.
Along the identity, a transport datum whose common cover maps to the source torsor compatibly with
a cover map `a : Y ⟶ Y'` and whose coefficient map is an equivariant map `c` gives the reduction
of coefficients along `c` followed by the inverse of the cover comparison of `a`. A transport
datum twisted by a deck element `g` of the source torsor, with coefficient map precomposed with
`g⁻¹`, gives the same transport map. See `EtaleAssociatedTransportLaws.md`.
-/

noncomputable section

universe u

namespace Langlands.Shimura.Coefficients

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Langlands.Geometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

variable {R : Type u} [CommRing R]

set_option hygiene false in
local notation "constant" Z:max => constantSheaf (Scheme.smallEtaleTopology Z) (ModuleCat.{u} R)

namespace EtaleTransportDatum

/-- Transport along the identity through a cover map: if the common cover maps by `w` to the
source torsor `Y` (after the identification of base change along the identity), the target cover
map factors as `w` followed by a cover map `a : Y ⟶ Y'`, and the coefficient map is the
equivariant map `c : M ⟶ M'`, then the transport map is the identification of the restriction
along the identity, followed by reduction of coefficients along `c` and the inverse of the cover
comparison of `a`. -/
theorem sheafMap_id_transition {X : Scheme.{u}} {G H : Type u} [Group G] [Group H]
    {Y : Action X.Etale G} {Y' : Action X.Etale H}
    {M : Action (ModuleCat.{u} R) G} {M' : Action (ModuleCat.{u} R) H}
    (t : EtaleTransportDatum (R := R) (𝟙 X) Y Y' M M') (hY' : IsFiniteGeometricTorsor X Y')
    (ψ : G →* H) (a : Y ⟶ (Action.res X.Etale ψ).obj Y')
    (c : M ⟶ (Action.res (ModuleCat.{u} R) ψ).obj M')
    [IsIso (etaleCrossCoverMap X ψ a (𝟙 ((Action.res (ModuleCat.{u} R) ψ).obj M')))]
    (w : t.cover.V ⟶ Y.V) (hw : t.toSource ≫ etaleTorsorPullbackIdMap X Y = w)
    (ht : w ≫ a.hom = t.toTarget) (hc : t.coefficient = c.hom) :
    t.sheafMap hY' = (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app _ ≫
      (etaleAssociatedFunctor X Y).map c ≫
      inv (etaleCrossCoverMap X ψ a (𝟙 ((Action.res (ModuleCat.{u} R) ψ).obj M'))) := by
  apply t.hom_ext hY'
  rw [t.sheafMap_inclusion, etaleConstantAssociatedPullback_id_assoc,
    reassoc_of% etaleCrossCoverMap_id_inclusion_self (Y := Y)
      (Y' := (etaleTorsorPullbackFunctor (𝟙 X) G).obj Y) ((etaleTorsorPullbackId X G).hom.app Y)
      (etaleTorsorPullbackIdMap X Y) rfl M,
    ← coverPullback_comp_assoc, hw, ← ht, coverPullback_comp, Category.assoc, Category.assoc,
    ← reassoc_of% (etaleCrossCoverMap_id_inclusion ψ a a.hom rfl M'), IsIso.inv_hom_id_assoc,
    etaleAssociatedInclusion_natural_assoc, hc]
  change _ ≫ _ ≫ _ ≫ _ = (EtalePullback.restrictionId (ModuleCat.{u} R)).hom.app
    ((etaleAssociatedFunctor X Y).obj M) ≫ _
  congr 2
  exact (coverPullback_natural (R := R) (Scheme.smallEtaleTopology X) w
    ((constant X).map c.hom))

/-- Twisting a transport datum by a deck element: if the common covers are related by `w`
compatibly with the target cover maps, the source cover map of `t₂` corresponds to that of `t₁`
followed by the deck transformation of `g` on the base change of the source torsor, and the
coefficient map of `t₂` is that of `t₁` precomposed with the action of `g⁻¹`, then the two
transport maps agree. -/
theorem sheafMap_eq_of_twist {X Z : Scheme.{u}} {f : Z ⟶ X} [Etale f] {G H : Type u} [Group G]
    [Group H] {Y : Action X.Etale G} {Y' : Action Z.Etale H}
    {M : Action (ModuleCat.{u} R) G} {M' : Action (ModuleCat.{u} R) H}
    (t₁ t₂ : EtaleTransportDatum (R := R) f Y Y' M M') (hY' : IsFiniteGeometricTorsor Z Y')
    (w : t₁.cover.V ⟶ t₂.cover.V) (g : G)
    (hs : w ≫ t₂.toSource = t₁.toSource ≫ ((etaleTorsorPullbackFunctor f G).obj Y).ρ g)
    (ht : w ≫ t₂.toTarget = t₁.toTarget) (hc : t₂.coefficient = M.ρ g⁻¹ ≫ t₁.coefficient) :
    t₂.sheafMap hY' = t₁.sheafMap hY' := by
  apply t₁.hom_ext hY'
  have hinv : etaleAssociatedInclusion Z ((etaleTorsorPullbackFunctor f G).obj Y) M ≫
      coverPullback (Scheme.smallEtaleTopology Z) (((etaleTorsorPullbackFunctor f G).obj Y).ρ g)
        ((constant Z).obj M.V) ≫
      (productSheaf (Scheme.smallEtaleTopology Z) ((etaleTorsorPullbackFunctor f G).obj Y).V).map
        ((constant Z).map (M.ρ g⁻¹)) =
      etaleAssociatedInclusion Z ((etaleTorsorPullbackFunctor f G).obj Y) M := by
    have h := inclusion_invariant (Scheme.smallEtaleTopology Z)
      ((etaleTorsorPullbackFunctor f G).obj Y)
      (((constantSheaf (Scheme.smallEtaleTopology Z) (ModuleCat.{u} R)).mapAction G).obj M) g⁻¹
    change inclusion _ _ _ ≫
      deckMap _ (((etaleTorsorPullbackFunctor f G).obj Y).ρ g⁻¹⁻¹) _ ≫ _ = _ at h
    rw [inv_inv] at h
    exact h
  rw [t₁.sheafMap_inclusion, ← ht, coverPullback_comp, t₂.sheafMap_inclusion_assoc,
    ← coverPullback_natural, ← coverPullback_comp_assoc, hs, coverPullback_comp_assoc, hc,
    Functor.map_comp, Functor.map_comp, coverPullback_natural_assoc, reassoc_of% hinv]

end EtaleTransportDatum

end Langlands.Shimura.Coefficients
