/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Ga

/-!
# Direct images of `𝔾ₐ` and `𝔾ₘ`

For a morphism of schemes `g : X ⟶ Y` we construct the map `𝔾ₐ ⟶ g_* 𝔾ₐ` of étale sheaves on
`Y`, given on an étale `Y`-scheme `V` by pulling back functions along `V ×_Y X ⟶ V`, and show that
the pullback of `𝔾ₐ` along an étale morphism is `𝔾ₐ`. For the analogous map `𝔾ₘ ⟶ g_* 𝔾ₘ` we
show that it is an isomorphism over every open `V ⊆ Y` over which `g` is an isomorphism.

## Main statements

- `AlgebraicGeometry.Scheme.gaSheafToLowerStarGaSheaf`: the map `𝔾ₐ ⟶ g_* 𝔾ₐ`.
- `AlgebraicGeometry.Scheme.upperStarGaSheafIso`: `g^* 𝔾ₐ ≅ 𝔾ₐ` for étale `g`.
- `AlgebraicGeometry.Scheme.isIso_upperStar_map_gmSheafToLowerStarGmSheaf`: the map
  `𝔾ₘ ⟶ g_* 𝔾ₘ` is an isomorphism over an open over which `g` is an isomorphism.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}}

/-- The map `𝔾ₐ ⟶ g_* 𝔾ₐ` of sheaves on the small étale site of `Y`: on an étale `Y`-scheme `V`
it is the pullback of functions `Γ(V, 𝒪_V) ⟶ Γ(V ×_Y X, 𝒪)` along the first projection. -/
noncomputable def gaSheafToLowerStarGaSheaf (g : X ⟶ Y) :
    Y.gaSheaf ⟶ (Etale.lowerStar AddCommGrpCat.{u + 1} g).obj X.gaSheaf :=
  ⟨Functor.whiskerRight (etaleStructurePresheafToPullback g)
    (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
      AddCommGrpCat.uliftFunctor.{u + 1, u})⟩

lemma gaSheafToLowerStarGaSheaf_app_apply (g : X ⟶ Y) (V : Y.Etale)
    (a : Y.gaPresheaf.obj (op V)) :
    ((gaSheafToLowerStarGaSheaf g).hom.app (op V) a).down =
      (Limits.pullback.fst V.hom g).appTop a.down :=
  rfl

/-- The comparison map `g^* 𝔾ₐ ⟶ 𝔾ₐ`, the transpose of `gaSheafToLowerStarGaSheaf`. -/
noncomputable def upperStarGaSheafToGaSheaf (g : X ⟶ Y) :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gaSheaf ⟶ X.gaSheaf :=
  ((Etale.upperStarLowerStarAdjunction _ g).homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g)

/-- For an étale morphism `g`, the comparison map `g^* 𝔾ₐ ⟶ 𝔾ₐ` is an isomorphism: `g^*` is
restriction along `X.Etale ⥤ Y.Etale`, and an étale `X`-scheme has the same functions as an
`X`-scheme and as a `Y`-scheme. -/
theorem isIso_upperStarGaSheafToGaSheaf (g : X ⟶ Y) [hg : Etale g] :
    IsIso (upperStarGaSheafToGaSheaf g) := by
  let adj := Etale.localizationRestrictionLowerStarAdjunction AddCommGrpCat.{u + 1} g hg
  have h : upperStarGaSheafToGaSheaf g =
      (Etale.upperStarIsoLocalizationRestriction _ g hg).hom.app Y.gaSheaf ≫
        (adj.homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g) := by
    rw [upperStarGaSheafToGaSheaf, Adjunction.homEquiv_counit, Adjunction.homEquiv_counit,
      Etale.upperStarIsoLocalizationRestriction, ← Adjunction.leftAdjointUniq_hom_app_counit _ adj,
      NatTrans.naturality_assoc]
  rw [h]
  suffices IsIso ((adj.homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g)) from inferInstance
  suffices IsIso ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g))) from
    isIso_of_reflects_iso _ (sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
  suffices ∀ U, IsIso (((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g))).app U) from
    NatIso.isIso_of_isIso_app _
  intro U
  have : ((sheafToPresheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((adj.homEquiv _ _).symm (gaSheafToLowerStarGaSheaf g))).app U =
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).map (𝟙 _) := by
    change (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).map _ ≫
      (forget₂ CommRingCat RingCat ⋙ forget₂ RingCat AddCommGrpCat ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}).map _ ≫ 𝟙 _ = _
    rw [Category.comp_id, ← Functor.map_comp]
    congr 1
    change Scheme.Γ.map _ ≫ Scheme.Γ.map _ = _
    rw [← Functor.map_comp]
    refine (congrArg Scheme.Γ.map ?_).trans (Scheme.Γ.map_id _)
    apply Quiver.Hom.unop_inj
    exact Limits.pullback.lift_fst _ _ _
  rw [this]
  infer_instance

/-- The pullback of `𝔾ₐ` along an étale morphism is `𝔾ₐ`. -/
noncomputable def upperStarGaSheafIso (g : X ⟶ Y) [Etale g] :
    (Etale.upperStar AddCommGrpCat.{u + 1} g).obj Y.gaSheaf ≅ X.gaSheaf :=
  haveI := isIso_upperStarGaSheafToGaSheaf g
  asIso (upperStarGaSheafToGaSheaf g)

/-- **`𝔾ₘ ⟶ g_* 𝔾ₘ` over an open where `g` is an isomorphism.** Let `g : X ⟶ Y` be a morphism
and `V ⊆ Y` an open over which `g` restricts to an isomorphism. Then the restriction of
`𝔾ₘ ⟶ g_* 𝔾ₘ` to `V` is an isomorphism: for an étale `W ⟶ V` the projection
`W ×_Y X ⟶ W` is an isomorphism. -/
theorem isIso_upperStar_map_gmSheafToLowerStarGmSheaf (g : X ⟶ Y) (V : Y.Opens)
    [IsIso (g ∣_ V)] :
    IsIso ((Etale.upperStar AddCommGrpCat.{u + 1} V.ι).map (gmSheafToLowerStarGmSheaf g)) := by
  have hV : Etale V.ι := inferInstance
  refine (NatIso.isIso_map_iff
    (Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι hV) _).mpr ?_
  suffices IsIso ((sheafToPresheaf V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1}).map
      ((Etale.localizationRestriction AddCommGrpCat.{u + 1} V.ι hV).map
        (gmSheafToLowerStarGmSheaf g))) from
    isIso_of_reflects_iso _ (sheafToPresheaf V.toScheme.smallEtaleTopology AddCommGrpCat.{u + 1})
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ fun W ↦ ?_
  -- the projection `W ×_Y X ⟶ W` is an isomorphism
  have hpb := ((IsPullback.of_hasPullback W.unop.hom (g ∣_ V)).paste_vert
    (isPullback_morphismRestrict g V))
  have : IsIso (Limits.pullback.fst (W.unop.hom ≫ V.ι) g) := by
    rw [← hpb.isoPullback_inv_fst]
    infer_instance
  change IsIso (CommRingCat.unitsAddCommGrpULift.{u + 1, u}.map
    (Scheme.Γ.map (Limits.pullback.fst (W.unop.hom ≫ V.ι) g).op))
  infer_instance

end AlgebraicGeometry.Scheme
