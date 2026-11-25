/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-! # Nested open restriction and inverse-image units

Source: Stacks Project, Tag 03F3; open restriction unit compatibility.
-/

@[expose] public section

universe u u'
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Generalized to arbitrary coefficients from the abelian-group unit calculation.
private theorem restriction_unit_coefficients
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology A)
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar A f).obj F).obj.map ψ.op ≫
        ((Etale.upperStarIsoLocalizationRestriction A f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let ρ := (Etale.upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (Etale.upperStarLowerStarAdjunction A f)
      (Etale.localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((Etale.upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((Etale.localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the composition unit equation, after restriction.
-- Generalized to arbitrary coefficients from the abelian-group unit calculation.
private theorem composition_unit_coefficients
    (A : Type u') [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A] [HasSmallSiteSheafify A]
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology A)
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((Etale.upperStarLowerStarAdjunction A t).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar A t).obj F).obj.map ψ.op ≫
        ((Etale.upperStarComp A f g t ht).hom.app F).hom.app (op c) =
      ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op b) ≫
        ((Etale.upperStarLowerStarAdjunction A f).unit.app
          ((Etale.upperStar A g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((Etale.upperStar A f).obj
          ((Etale.upperStar A g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (Etale.upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, Etale.lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((Etale.upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, Etale.lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The section pullback unit between nested opens is restriction, after the specified
composition and localization comparisons.
Source: Stacks Project, Tag 03F3; steps 2 and 3 of
`lem-weil-pbc-etale-open-section-pullback` and `open_restriction_pullback_unit`.
(blueprint: lem-weil-pbc-nested-open-section-unit)

Proof: Evaluate the localization adjunction unit at vU and restrict along the
identity diagonal δ : bU → U ×_X U. The site adjunct of δ is the identity of vU,
so the unit followed by δ is the inverse U localization comparison. Next use the
map ψ = (i,id) : bV → U ×_X V. Its site adjunct is the inclusion f : vV → vU,
so the V unit followed by ψ and the V localization comparison is F(f).
The pullback composition comparison sends ψ to t followed by the pullback of δ:
check the two outer projections and the two inner projections by the pullback
universal property. Evaluate the inverse-image composition unit law at vU and
restrict along ψ. Naturality moves δ across the i unit, and the first identity
replaces the U unit followed by δ by the inverse U localization comparison.
Cancel the composition isomorphism, precompose with the U localization comparison,
and postcompose with the V localization comparison. The second identity gives the
claimed restriction map. No step uses nonemptiness or strict inclusion, so the
argument includes empty and equal opens. -/
theorem nestedOpenSection_unit {X : Scheme.{u}} (U V : X.Opens) (h : V ≤ U)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let bU := Scheme.Etale.mk (𝟙 U.toScheme)
    let bV := Scheme.Etale.mk (𝟙 V.toScheme)
    let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj bU
    let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.ι)).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk (X.homOfLE h)
      (by
        change X.homOfLE h ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 V.toScheme ≫ V.ι
        simpa only [Category.id_comp] using X.homOfLE_ι h) trivial
    let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (X.homOfLE h)).obj bU :=
      MorphismProperty.Over.homMk (pullback.lift (X.homOfLE h) (𝟙 V.toScheme)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (X.homOfLE h)).unit.app ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F)).hom.app
        (op bU) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} (X.homOfLE h)).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} U.ι).obj F)).obj.map t.op ≫
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} (X.homOfLE h) U.ι V.ι
        (X.homOfLE_ι h).symm).inv.app F).hom.app (op bV) ≫
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} V.ι
        inferInstance).hom.app F).hom.app (op bV) =
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} U.ι
        inferInstance).hom.app F).hom.app (op bU) ≫ F.obj.map f.op  := by
  dsimp only
  let A := AddCommGrpCat.{u + 1}
  let i := X.homOfLE h
  let bU := Scheme.Etale.mk (𝟙 U.toScheme)
  let bV := Scheme.Etale.mk (𝟙 V.toScheme)
  let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale U.ι)).obj bU
  let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.ι)).obj bV
  let f : vV ⟶ vU := MorphismProperty.Over.homMk i
    (by
      change i ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 V.toScheme ≫ V.ι
      simpa only [Category.id_comp] using X.homOfLE_ι h) trivial
  let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj bU :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 V.toScheme)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
  let δ : bU ⟶ (MorphismProperty.Over.pullback @Etale ⊤ U.ι).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 U.toScheme) (𝟙 U.toScheme)
      (by
        change 𝟙 U.toScheme ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 U.toScheme ≫ U.ι
        simp only [Category.id_comp])) (by simp [bU])
  let ψ : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ V.ι).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 V.toScheme)
      (by
        change i ≫ (𝟙 U.toScheme ≫ U.ι) = 𝟙 V.toScheme ≫ V.ι
        simpa only [Category.id_comp] using X.homOfLE_ι h)) (by simp [bV])
  let H := (Etale.upperStar A U.ι).obj F
  let ρU := ((sheafSections _ A).obj (op bU)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A U.ι inferInstance).app F)
  let ρV := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A V.ι inferInstance).app F)
  let C := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarComp A i U.ι V.ι (X.homOfLE_ι h).symm).app F)
  have hδ : ((Etale.upperStarLowerStarAdjunction A U.ι).unit.app F).hom.app (op vU) ≫
      H.obj.map δ.op = ρU.inv := by
    have q := restriction_unit_coefficients A U.ι F vU bU δ
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ U.ι inferInstance
        _root_.trivial).homEquiv bU vU).symm δ = 𝟙 vU := by
      ext
      simp [δ, Adjunction.homEquiv_counit]
      rfl
    rw [hd, op_id] at q
    erw [F.obj.map_id] at q
    exact (Iso.eq_comp_inv ρU).2 q
  have hψ : ((Etale.upperStarLowerStarAdjunction A V.ι).unit.app F).hom.app (op vU) ≫
      ((Etale.upperStar A V.ι).obj F).obj.map ψ.op ≫ ρV.hom = F.obj.map f.op := by
    have q := restriction_unit_coefficients A V.ι F vU bV ψ
    have hp : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ V.ι inferInstance
        _root_.trivial).homEquiv bV vU).symm ψ = f := by
      ext
      simp [ψ, f, Adjunction.homEquiv_counit]
    rw [hp] at q
    exact q
  have hχ : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      i U.ι V.ι (X.homOfLE_ι h).symm).hom.app vU =
      t ≫ (MorphismProperty.Over.pullback @Etale ⊤ i).map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      i U.ι V.ι (X.homOfLE_ι h).symm).hom.app vU).left =
        t.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ i).map δ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
          limit.lift_π, PullbackCone.mk_π_app, Category.comp_id, limit.lift_π_assoc,
          cospan_left, vU, bU, ψ, t, δ]
        exact (Category.comp_id i).symm
      · simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
          MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
          Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
          limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
          limit.lift_π, cospan_left, vU, bU, ψ, t, δ]
        exact (Category.id_comp i).trans (Category.comp_id i).symm
    · simp [ψ, t, δ, bU, vU, MorphismProperty.Over.pullback,
        MorphismProperty.Over.mk, Category.assoc]
  have hc := composition_unit_coefficients A i U.ι V.ι (X.homOfLE_ι h).symm F vU bV ψ
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((Etale.upperStarLowerStarAdjunction A U.ι).unit.app F).hom.app (op vU) ≫
    ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ U.ι).obj vU)) ≫
    ((Etale.lowerStar A i).obj ((Etale.upperStar A i).obj H)).obj.map δ.op ≫
    ((Etale.upperStar A i).obj H).obj.map t.op at hc
  erw [← ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.naturality_assoc] at hc
  erw [reassoc_of% hδ] at hc
  have hc' : (ρU.inv ≫
      ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.app (op bU) ≫
      ((Etale.upperStar A i).obj H).obj.map t.op) ≫ C.inv =
      ((Etale.upperStarLowerStarAdjunction A V.ι).unit.app F).hom.app (op vU) ≫
        ((Etale.upperStar A V.ι).obj F).obj.map ψ.op :=
    (Iso.comp_inv_eq C).2 hc.symm
  have q := congrArg (fun z ↦ ρU.hom ≫ z ≫ ρV.hom) hc'
  simp only [Category.assoc] at q
  erw [reassoc_of% ρU.hom_inv_id, hψ] at q
  exact q


end AlgebraicGeometry
