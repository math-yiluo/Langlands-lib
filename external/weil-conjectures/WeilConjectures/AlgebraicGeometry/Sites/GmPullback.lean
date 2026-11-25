/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.Gm
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# The pullback comparison maps of `𝔾ₘ` are compatible with composition

For `g : X ⟶ Y` the comparison map `g^* 𝔾ₘ ⟶ 𝔾ₘ`
(`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf`) is the transpose of the map
`𝔾ₘ ⟶ g_* 𝔾ₘ` given by pulling back units along the projections `V ×_Y X ⟶ V`. For
`a : X ⟶ Y` and `b : Y ⟶ Z`, the comparison map of `a ≫ b` is the composite

`(a ≫ b)^* 𝔾ₘ ≅ a^* b^* 𝔾ₘ ⟶ a^* 𝔾ₘ ⟶ 𝔾ₘ`

(`AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf_comp`): on sections this is the
compatibility of the projections `V ×_Z X ≅ (V ×_Z Y) ×_Y X ⟶ V ×_Z Y ⟶ V` with the projection
`V ×_Z X ⟶ V`.

## Main statements

- `AlgebraicGeometry.Scheme.gmSheafToLowerStarGmSheaf_comp`: the compatibility of the maps
  `𝔾ₘ ⟶ g_* 𝔾ₘ` with composition.
- `AlgebraicGeometry.Scheme.upperStarGmSheafToGmSheaf_comp`: the compatibility of the
  comparison maps `g^* 𝔾ₘ ⟶ 𝔾ₘ` with composition.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry

namespace Scheme

variable {X Y Z : Scheme.{u}}

/-- The maps `𝔾ₘ ⟶ g_* 𝔾ₘ` are compatible with composition: for `a : X ⟶ Y` and `b : Y ⟶ Z`,
the map for `a ≫ b` is `𝔾ₘ ⟶ b_* 𝔾ₘ ⟶ b_* a_* 𝔾ₘ ≅ (a ≫ b)_* 𝔾ₘ`. -/
lemma gmSheafToLowerStarGmSheaf_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    gmSheafToLowerStarGmSheaf b ≫ (Etale.lowerStar _ b).map (gmSheafToLowerStarGmSheaf a) ≫
        (Etale.lowerStarComp _ a b).hom.app X.gmSheaf =
      gmSheafToLowerStarGmSheaf (a ≫ b) := by
  apply Sheaf.hom_ext
  ext V x
  apply ULift.ext
  apply Additive.toMul.injective
  apply Units.ext
  rw [InducedCategory.comp_hom, InducedCategory.comp_hom, NatTrans.comp_app, NatTrans.comp_app,
    Etale.lowerStarComp_hom_app_hom_app]
  change (((MorphismProperty.Over.pullbackComp a b).hom.app V.unop).left).appTop
      ((pullback.fst (pullback.snd V.unop.hom b) a).appTop
        ((pullback.fst V.unop.hom b).appTop _)) = (pullback.fst V.unop.hom (a ≫ b)).appTop _
  have h := congrArg (fun φ ↦ φ.appTop.hom ((Additive.toMul x.down : Γ(V.unop.left, ⊤)ˣ) :
    Γ(V.unop.left, ⊤))) (MorphismProperty.Over.pullbackComp_left_fst_fst a b V.unop)
  simp only [Scheme.Hom.comp_appTop, CommRingCat.comp_apply] at h
  exact h

/-- The comparison maps `g^* 𝔾ₘ ⟶ 𝔾ₘ` are compatible with composition: for `a : X ⟶ Y` and
`b : Y ⟶ Z`, the comparison map of `a ≫ b` is `(a ≫ b)^* 𝔾ₘ ≅ a^* b^* 𝔾ₘ ⟶ a^* 𝔾ₘ ⟶ 𝔾ₘ`. -/
lemma upperStarGmSheafToGmSheaf_comp (a : X ⟶ Y) (b : Y ⟶ Z) :
    (Etale.upperStarComp _ a b).hom.app Z.gmSheaf ≫
        (Etale.upperStar _ a).map (upperStarGmSheafToGmSheaf b) ≫ upperStarGmSheafToGmSheaf a =
      upperStarGmSheafToGmSheaf (a ≫ b) := by
  have ha : (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app Y.gmSheaf ≫
      (Etale.lowerStar _ a).map (upperStarGmSheafToGmSheaf a) =
      gmSheafToLowerStarGmSheaf a := by
    have := ((Etale.upperStarLowerStarAdjunction _ a).homEquiv _ _).apply_symm_apply
      (gmSheafToLowerStarGmSheaf a)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  have hb : (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} b).unit.app Z.gmSheaf ≫
      (Etale.lowerStar _ b).map (upperStarGmSheafToGmSheaf b) =
      gmSheafToLowerStarGmSheaf b := by
    have := ((Etale.upperStarLowerStarAdjunction _ b).homEquiv _ _).apply_symm_apply
      (gmSheafToLowerStarGmSheaf b)
    rw [Adjunction.homEquiv_unit] at this
    exact this
  apply ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} (a ≫ b)).homEquiv _ _).injective
  conv_rhs => rw [upperStarGmSheafToGmSheaf, Equiv.apply_symm_apply]
  rw [← gmSheafToLowerStarGmSheaf_comp a b, Adjunction.homEquiv_unit, Functor.map_comp,
    ← Category.assoc, Etale.upperStarComp_hom_app_unit_app AddCommGrpCat.{u + 1} a b,
    Category.assoc]
  erw [← (Etale.lowerStarComp AddCommGrpCat.{u + 1} a b).hom.naturality]
  simp only [← Category.assoc]
  refine congrArg (· ≫ _) ?_
  rw [Adjunction.comp_unit_app, Category.assoc]
  erw [← Functor.map_comp]
  rw [Functor.map_comp (Etale.lowerStar _ a),
    ← Category.assoc ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app _)]
  have hn : (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app _ ≫
      (Etale.lowerStar _ a).map ((Etale.upperStar _ a).map (upperStarGmSheafToGmSheaf b)) =
      upperStarGmSheafToGmSheaf b ≫
        (Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.app _ :=
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} a).unit.naturality _).symm
  rw [hn]
  rw [Category.assoc]
  erw [ha]
  rw [Functor.map_comp, ← Category.assoc, hb]

end Scheme

end AlgebraicGeometry
