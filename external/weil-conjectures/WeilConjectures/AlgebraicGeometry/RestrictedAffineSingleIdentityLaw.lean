/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleMaps
import WeilConjectures.AlgebraicGeometry.RestrictedAffineSingleUnitLift

/-! # Explicit maps for restricted degree-zero complexes

Source: Stacks Project, Tags 09Z1 and 0EZM.
-/

@[expose] public section

universe v
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale

namespace AlgebraicGeometry.Etale

private lemma comp_congr {T S R : Scheme.{v}} (a : T ⟶ S) (b : S ⟶ R)
    (d d' : T ⟶ R) (hd : d = a ≫ b) (hd' : d' = a ≫ b) (h : d = d') :
    upperStarComp AddCommGrpCat.{v + 1} a b d hd =
      eqToIso (by rw [h]) ≪≫ upperStarComp AddCommGrpCat.{v + 1} a b d' hd' := by
  subst h
  simp

private lemma unit_square {X Y : Scheme.{v}} (r : X ⟶ Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    (upperStarComp AddCommGrpCat.{v + 1} (𝟙 X) r).inv.app F ≫
      (upperStarComp AddCommGrpCat.{v + 1} r (𝟙 Y) ((𝟙 X) ≫ r)
        (by simp)).hom.app F ≫
      (upperStar AddCommGrpCat.{v + 1} r).map
        ((upperStarId AddCommGrpCat.{v + 1} Y).hom.app F) =
      (upperStarId AddCommGrpCat.{v + 1} X).hom.app
        ((upperStar AddCommGrpCat.{v + 1} r).obj F) := by
  rw [comp_congr (𝟙 X) r _ r rfl
    (by simp) (by simp),
    comp_congr r (𝟙 Y) _ r
      (by simp) (by simp) (by simp)]
  simp only [Iso.trans_inv, Iso.trans_hom, NatTrans.comp_app, Category.assoc,
    Iso.inv_hom_id_app_assoc]
  rw [upperStarComp_id_left, upperStarComp_id_right]
  simp

private lemma unit_square_heq {X Y : Scheme.{v}} (q : X ⟶ X) (hq : q = 𝟙 X)
    (r : X ⟶ Y) (hw : q ≫ r = r ≫ 𝟙 Y)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1}) :
    HEq ((upperStarComp AddCommGrpCat.{v + 1} q r).inv.app F ≫
      (upperStarComp AddCommGrpCat.{v + 1} r (𝟙 Y) (q ≫ r) hw).hom.app F ≫
      (upperStar AddCommGrpCat.{v + 1} r).map
        ((upperStarId AddCommGrpCat.{v + 1} Y).hom.app F))
      ((upperStarId AddCommGrpCat.{v + 1} X).hom.app
        ((upperStar AddCommGrpCat.{v + 1} r).obj F)) := by
  subst q
  exact heq_of_eq (unit_square r F)

private lemma raw_identity {S Y : Scheme.{v}} (a : Y ⟶ Y)
    (ha : a = 𝟙 Y) (h : Y ⟶ S) (w : a ≫ h = h)
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : (upperStar AddCommGrpCat.{v + 1} a).obj F ⟶ F)
    (hφ : HEq φ ((upperStarId AddCommGrpCat.{v + 1} Y).hom.app F))
    (U : S.Etale) :
    HEq (rawAffineRestrictedCoefficient a h h w F F φ U)
      ((upperStarId AddCommGrpCat.{v + 1} (pullback U.hom h)).hom.app
        ((upperStar AddCommGrpCat.{v + 1} (pullback.snd U.hom h)).obj F)) := by
  subst a
  have he : φ = (upperStarId AddCommGrpCat.{v + 1} Y).hom.app F := eq_of_heq hφ
  subst φ
  unfold rawAffineRestrictedCoefficient
  have hq : rawAffineRestrictedMap (𝟙 Y) h h w U = 𝟙 _ := by
    apply pullback.hom_ext <;> simp [rawAffineRestrictedMap]
  exact unit_square_heq _ hq (pullback.snd U.hom h) _ F

/-- Identity law for restricted single transitions.
Source: Stacks Project, Tags 09Z1 and 03CB, inverse-image coherence in restriction.
(blueprint: lem-sbc-restricted-affine-single-identity-law).

Proof: Expand the transition as the single comparison followed by the image of the
restricted coefficient. The pullback second-projection equation gives its commuting
square. Use D.map_id to replace both horizontal arrows by identities, and hφid to
replace the original coefficient with upperStarId. The identity square comparison
is the composite of the two unit comparisons, whiskered along the second projection.
Its inverse cancels the pulled-back coefficient unit, leaving the unit on the
restricted sheaf, transported along restrictedAffineDiagram.map_id. Apply
HomologicalComplex.hom_ext. At degree zero use singleObjXSelf and naturality of the
unit comparison to identify the single-complex map with this sheaf equality. At all
other degrees the target single complex is zero, so its morphisms agree. The
calculation also applies to zero sheaves and empty schemes; for an empty index type
there is no identity equation to check. -/
theorem restrictedAffineSingleTransition_identity_law {S : Scheme.{v}}
    {I : Type v} [Preorder I]
    (D : Iᵒᵖ ⥤ Over S)
    (F : ∀ i : I, Sheaf (D.obj (op i)).left.smallEtaleTopology AddCommGrpCat.{v + 1})
    (φ : ∀ {i j : I} (f : i ⟶ j),
      (((D.map f.op).left)^*[AddCommGrpCat.{v + 1}]).obj (F i) ⟶ F j)
    (hφid : ∀ i : I, HEq (φ (𝟙 i))
      ((upperStarId AddCommGrpCat.{v + 1} (D.obj (op i)).left).hom.app (F i)))
    (U : S.Etale) :
    let D' := restrictedAffineDiagram D U
    let K := restrictedAffineK D F U
    let ψ := fun {i j : Iᵒᵖ} (f : j ⟶ i) ↦ restrictedAffineSingleTransition D F φ U f
    ( ∀ i : Iᵒᵖ, ψ (𝟙 i) =
      (NatIso.mapHomologicalComplex
        (eqToIso (congrArg (upperStar AddCommGrpCat.{v + 1}) (D'.map_id i)))
        (ComplexShape.up ℤ)).hom.app (K i) ≫
      (NatIso.mapHomologicalComplex (upperStarId AddCommGrpCat.{v + 1} (D'.obj i))
        (ComplexShape.up ℤ)).hom.app (K i)) := by
  intro D' K ψ i
  have ha : (D.map (𝟙 i)).left = 𝟙 (D.obj i).left := by
    rw [D.map_id]
    rfl
  have hraw := raw_identity (D.map (𝟙 i)).left ha (D.obj i).hom
    (Over.w (D.map (𝟙 i))) (F i.unop) (φ (𝟙 i).unop) (hφid i.unop) U
  exact restrictedAffineSingleUnit_lift D F φ U i hraw

end AlgebraicGeometry.Etale
