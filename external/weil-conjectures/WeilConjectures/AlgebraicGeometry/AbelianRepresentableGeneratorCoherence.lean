/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CyclicDerivedHomComparisonMap
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.AlgebraicGeometry.ConstantSectionAdjunctPullback

/-! # Naturality of the abelian representable generator

Source: Stacks Project, Tag 03Q8, and the free-sheaf adjunction.
The proof uses inverse-image units to compare sections on arbitrary etale objects.
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
private theorem etaleSection_unit {X T S : Scheme.{u}}
    (r : T ⟶ X) (s : S ⟶ X) [Etale r] [Etale s]
    (j : S ⟶ T) (hf : s = j ≫ r)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    let bU := Scheme.Etale.mk (𝟙 T)
    let bV := Scheme.Etale.mk (𝟙 S)
    let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale r)).obj bU
    let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale s)).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk (j)
      (by
        change j ≫ (𝟙 T ≫ r) = 𝟙 S ≫ s
        simpa only [Category.id_comp] using hf.symm) trivial
    let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ (j)).obj bU :=
      MorphismProperty.Over.homMk (pullback.lift (j) (𝟙 S)
        ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1}
      (j)).unit.app ((Etale.upperStar AddCommGrpCat.{u + 1} r).obj F)).hom.app
        (op bU) ≫
      ((Etale.upperStar AddCommGrpCat.{u + 1} (j)).obj
        ((Etale.upperStar AddCommGrpCat.{u + 1} r).obj F)).obj.map t.op ≫
      ((Etale.upperStarComp AddCommGrpCat.{u + 1} (j) r s
        hf).inv.app F).hom.app (op bV) ≫
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} s
        inferInstance).hom.app F).hom.app (op bV) =
      ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} r
        inferInstance).hom.app F).hom.app (op bU) ≫ F.obj.map f.op  := by
  dsimp only
  let A := AddCommGrpCat.{u + 1}
  let i := j
  let bU := Scheme.Etale.mk (𝟙 T)
  let bV := Scheme.Etale.mk (𝟙 S)
  let vU : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale r)).obj bU
  let vV : X.Etale := (MorphismProperty.Over.map ⊤ (inferInstance : Etale s)).obj bV
  let f : vV ⟶ vU := MorphismProperty.Over.homMk i
    (by
      change i ≫ (𝟙 T ≫ r) = 𝟙 S ≫ s
      simpa only [Category.id_comp] using hf.symm) trivial
  let t : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ i).obj bU :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 S)
      ((Category.comp_id _).trans (Category.id_comp _).symm)) (by simp [bU, bV])
  let δ : bU ⟶ (MorphismProperty.Over.pullback @Etale ⊤ r).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 T) (𝟙 T)
      (by
        change 𝟙 T ≫ (𝟙 T ≫ r) = 𝟙 T ≫ r
        simp only [Category.id_comp])) (by simp [bU])
  let ψ : bV ⟶ (MorphismProperty.Over.pullback @Etale ⊤ s).obj vU :=
    MorphismProperty.Over.homMk (pullback.lift i (𝟙 S)
      (by
        change i ≫ (𝟙 T ≫ r) = 𝟙 S ≫ s
        simpa only [Category.id_comp] using hf.symm)) (by simp [bV])
  let H := (Etale.upperStar A r).obj F
  let ρU := ((sheafSections _ A).obj (op bU)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A r inferInstance).app F)
  let ρV := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarIsoLocalizationRestriction A s inferInstance).app F)
  let C := ((sheafSections _ A).obj (op bV)).mapIso
    ((Etale.upperStarComp A i r s hf).app F)
  have hδ : ((Etale.upperStarLowerStarAdjunction A r).unit.app F).hom.app (op vU) ≫
      H.obj.map δ.op = ρU.inv := by
    have q := restriction_unit_coefficients A r F vU bU δ
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ r inferInstance
        _root_.trivial).homEquiv bU vU).symm δ = 𝟙 vU := by
      ext
      simp [δ, Adjunction.homEquiv_counit]
      rfl
    rw [hd, op_id] at q
    erw [F.obj.map_id] at q
    exact (Iso.eq_comp_inv ρU).2 q
  have hψ : ((Etale.upperStarLowerStarAdjunction A s).unit.app F).hom.app (op vU) ≫
      ((Etale.upperStar A s).obj F).obj.map ψ.op ≫ ρV.hom = F.obj.map f.op := by
    have q := restriction_unit_coefficients A s F vU bV ψ
    have hp : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ s inferInstance
        _root_.trivial).homEquiv bV vU).symm ψ = f := by
      ext
      simp [ψ, f, Adjunction.homEquiv_counit]
    rw [hp] at q
    exact q
  have hχ : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      i r s hf).hom.app vU =
      t ≫ (MorphismProperty.Over.pullback @Etale ⊤ i).map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      i r s hf).hom.app vU).left =
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
  have hc := composition_unit_coefficients A i r s hf F vU bV ψ
  rw [hχ, op_comp, Functor.map_comp] at hc
  change _ = ((Etale.upperStarLowerStarAdjunction A r).unit.app F).hom.app (op vU) ≫
    ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ r).obj vU)) ≫
    ((Etale.lowerStar A i).obj ((Etale.upperStar A i).obj H)).obj.map δ.op ≫
    ((Etale.upperStar A i).obj H).obj.map t.op at hc
  erw [← ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.naturality_assoc] at hc
  erw [reassoc_of% hδ] at hc
  have hc' : (ρU.inv ≫
      ((Etale.upperStarLowerStarAdjunction A i).unit.app H).hom.app (op bU) ≫
      ((Etale.upperStar A i).obj H).obj.map t.op) ≫ C.inv =
      ((Etale.upperStarLowerStarAdjunction A s).unit.app F).hom.app (op vU) ≫
        ((Etale.upperStar A s).obj F).obj.map ψ.op :=
    (Iso.comp_inv_eq C).2 hc.symm
  have q := congrArg (fun z ↦ ρU.hom ≫ z ≫ ρV.hom) hc'
  simp only [Category.assoc] at q
  erw [reassoc_of% ρU.hom_inv_id, hψ] at q
  exact q

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem etaleSection_pullback {X T S : Scheme.{u}}
    (r : T ⟶ X) (s : S ⟶ X) [Etale r] [Etale s]
    (j : S ⟶ T) (hf : s = j ≫ r)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (m : (constantSheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (Etale.upperStar AddCommGrpCat.{u + 1} r).obj F) :
    let bU := Scheme.Etale.mk (𝟙 T)
    let bV := Scheme.Etale.mk (𝟙 S)
    let vU := (MorphismProperty.Over.map ⊤ (inferInstance : Etale r)).obj bU
    let vV := (MorphismProperty.Over.map ⊤ (inferInstance : Etale s)).obj bV
    let f : vV ⟶ vU := MorphismProperty.Over.homMk (j)
      (by
        change j ≫ (𝟙 T ≫ r) = 𝟙 S ≫ s
        simpa only [Category.id_comp] using hf.symm) trivial
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj S.smallEtaleTopology AddCommGrpCat.{u + 1}
        (show IsTerminal bV from IsTerminal.ofUniqueHom
          (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
          (fun a f ↦ by
            apply MorphismProperty.Over.Hom.ext
            exact (Category.comp_id _).symm.trans (MorphismProperty.Over.w f)))).homEquiv _ _
        ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
          (j)).inv.app (AddCommGrpCat.of (ULift ℤ)) ≫
          (Etale.upperStar AddCommGrpCat.{u + 1} (j)).map m ≫
          (Etale.upperStarComp AddCommGrpCat.{u + 1} (j) r s
            hf).inv.app F)) =
      (((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} s
        inferInstance).inv.app F).hom.app (op bV))
        (F.obj.map f.op
          ((((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} r
            inferInstance).hom.app F).hom.app (op bU))
            (AddCommGrpCat.uliftZMultiplesAddEquiv _
              ((constantSheafAdj T.smallEtaleTopology AddCommGrpCat.{u + 1}
                (show IsTerminal bU from IsTerminal.ofUniqueHom
                  (fun a ↦ MorphismProperty.Over.homMk a.hom (Category.comp_id _))
                  (fun a f ↦ by
                    apply MorphismProperty.Over.Hom.ext
                    exact (Category.comp_id _).symm.trans
                      (MorphismProperty.Over.w f)))).homEquiv _ _ m)))) := by
  dsimp only
  simp only [← Category.assoc]
  rw [Adjunction.homEquiv_naturality_right]
  rw [constantSection_adjunct_pullback]
  have hz {B C : AddCommGrpCat.{u + 1}}
      (f : AddCommGrpCat.of (ULift.{u + 1} ℤ) ⟶ B) (g : B ⟶ C) :
      AddCommGrpCat.uliftZMultiplesAddEquiv C (f ≫ g) =
        g (AddCommGrpCat.uliftZMultiplesAddEquiv B f) := by rfl
  rw [hz, hz]
  have hn := etaleSection_unit r s j hf F
  dsimp only at hn
  let e := Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} s
    (inferInstance : Etale s)
  have hinv : (e.hom.app F).hom.app (op (Scheme.Etale.mk (𝟙 S))) ≫
      (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 S))) = 𝟙 _ := by
    exact (((sheafSections S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (op (Scheme.Etale.mk (𝟙 S)))).mapIso (e.app F)).hom_inv_id
  have hn' := congrArg
    (fun q ↦ q ≫ (e.inv.app F).hom.app (op (Scheme.Etale.mk (𝟙 S)))) hn
  dsimp only [e] at hinv hn'
  simp only [Category.assoc, hinv, Category.comp_id] at hn'
  exact ConcreteCategory.congr_hom hn' _

namespace Etale

set_option backward.isDefEq.respectTransparency false in
/-- Precomposition with the free-representable map is restriction of sections.
This is naturality of the sheafification and free-abelian adjunctions, followed
by naturality of the universe-lifted Yoneda equivalence. -/
private lemma sectionsEquiv_precomp {X : Scheme.{u}} {A B : X.Etale}
    (a : A ⟶ B) (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (f : (etaleOpenFreeSheaf X).obj B ⟶ F) :
    EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology A F
      ((etaleOpenFreeSheaf X).map a ≫ f) =
      F.obj.map a.op (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology B F f) := by
  change EtaleOpenComparison.freeSectionsEquiv A F.obj
    ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv _ _
      ((presheafToSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).map
        (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map
          (uliftYoneda.map a)) ≫ f)) = _
  rw [Adjunction.homEquiv_naturality_left]
  change uliftYonedaEquiv (((AddCommGrpCat.adj.whiskerRight X.Etaleᵒᵖ).homEquiv _ _)
    (((Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free).map (uliftYoneda.map a) ≫
      ((sheafificationAdjunction X.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
        _ _ f))) = _
  rw [Adjunction.homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality _ a.op).symm

private noncomputable def generatorSection {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W : X.Etale) :
    ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)).obj.obj
      (op ((MorphismProperty.Over.map ⊤
        (inferInstance : AlgebraicGeometry.Etale (pullback.fst h W.hom))).obj
          (abelianEtaleFinal (pullback h W.hom)))) := by
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)
  let B := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W
  let R : Y.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst h W.hom) inferInstance
  let i : R ≅ B := MorphismProperty.Over.isoMk (pullbackSymmetry h W.hom) (by
    dsimp [B, R]
    simp)
  let z := abelianRepresentableHomEquiv W _
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
      ((abelianRepresentable X).obj W))
  let O := (MorphismProperty.Over.map ⊤
    (inferInstance : AlgebraicGeometry.Etale (pullback.fst h W.hom))).obj
      (abelianEtaleFinal (pullback h W.hom))
  let j : O ≅ R := MorphismProperty.Over.isoMk (Iso.refl _) (by
    dsimp [O, abelianEtaleFinal, R]
    exact (Category.id_comp _).symm)
  exact A.obj.map j.hom.op (A.obj.map i.hom.op z)

private noncomputable def generatorArrow {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W : X.Etale) :
    (MorphismProperty.Over.map ⊤
      (inferInstance : AlgebraicGeometry.Etale (pullback.fst h W.hom))).obj
        (abelianEtaleFinal (pullback h W.hom)) ⟶
      (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W := by
  let B := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W
  let R : Y.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst h W.hom) inferInstance
  let i : R ≅ B := MorphismProperty.Over.isoMk (pullbackSymmetry h W.hom) (by
    dsimp [B, R]
    simp)
  let O := (MorphismProperty.Over.map ⊤
    (inferInstance : AlgebraicGeometry.Etale (pullback.fst h W.hom))).obj
      (abelianEtaleFinal (pullback h W.hom))
  let j : O ≅ R := MorphismProperty.Over.isoMk (Iso.refl _) (by
    dsimp [O, abelianEtaleFinal, R]
    exact (Category.id_comp _).symm)
  exact j.hom ≫ i.hom

private theorem generatorSection_eq {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    generatorSection h W =
      ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)).obj.map
        (generatorArrow h W).op (abelianRepresentableHomEquiv W _
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
            ((abelianRepresentable X).obj W))) := by
  dsimp only [generatorSection, generatorArrow]
  rw [op_comp, Functor.map_comp]
  rfl

private theorem generator_adjunct {X Y : Scheme.{u}} (h : Y ⟶ X) (W : X.Etale) :
    AddCommGrpCat.uliftZMultiplesAddEquiv _
      ((constantSheafAdj (pullback h W.hom).smallEtaleTopology AddCommGrpCat.{u + 1}
        (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _)).homEquiv _ _
          (abelianRepresentableGenerator h W)) =
      ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1}
        (pullback.fst h W.hom) inferInstance).inv.app _).hom.app
          (op (abelianEtaleFinal (pullback h W.hom))) (generatorSection h W) := by
  unfold abelianRepresentableGenerator
  simp only [Sheaf.H.equiv₀, AddEquiv.symm_trans_apply,
    AddEquiv.apply_symm_apply, ← Adjunction.homAddEquiv_apply]
  erw [AddEquiv.apply_symm_apply]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem generatorSection_naturality {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W V : X.Etale) (v : V ⟶ W) :
    let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
    let rW := pullback.fst h W.hom
    let rV := pullback.fst h V.hom
    let bW := (MorphismProperty.Over.map ⊤
      (inferInstance : AlgebraicGeometry.Etale rW)).obj (abelianEtaleFinal _)
    let bV := (MorphismProperty.Over.map ⊤
      (inferInstance : AlgebraicGeometry.Etale rV)).obj (abelianEtaleFinal _)
    let f : bV ⟶ bW := MorphismProperty.Over.homMk g (by
      change g ≫ (𝟙 _ ≫ rW) = 𝟙 _ ≫ rV
      rw [Category.id_comp, Category.id_comp]
      exact pullback.lift_fst _ _ _)
    let a := (upperStar AddCommGrpCat.{u + 1} h).map ((abelianRepresentable X).map v)
    a.hom.app (op bV) (generatorSection h V) =
      ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)).obj.map
        f.op (generatorSection h W) := by
  dsimp only
  let U := upperStar AddCommGrpCat.{u + 1} h
  let B := MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h
  let A := (abelianRepresentable X).obj W
  let C := (abelianRepresentable X).obj V
  let a := U.map ((abelianRepresentable X).map v)
  have hn : a.hom.app (op (B.obj V))
      (abelianRepresentableHomEquiv V _
        ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app C)) =
      (U.obj A).obj.map (B.map v).op
        (abelianRepresentableHomEquiv W _
          ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app A)) := by
    have hc := (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit_naturality
      ((abelianRepresentable X).map v)
    have hc₁ := EtaleOpenComparison.sectionsEquiv_naturality X.smallEtaleTopology V
      ((lowerStar AddCommGrpCat.{u + 1} h).map a)
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app C)
    have hc₂ := sectionsEquiv_precomp v ((lowerStar AddCommGrpCat.{u + 1} h).obj
      (U.obj A)) ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app A)
    exact hc₁.symm.trans ((congrArg (abelianRepresentableHomEquiv V _) hc).trans hc₂)
  rw [generatorSection_eq, generatorSection_eq]
  rw [NatTrans.naturality_apply a.hom (generatorArrow h V).op]
  rw [hn]
  let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
  let bW := (MorphismProperty.Over.map ⊤
    (inferInstance : AlgebraicGeometry.Etale (pullback.fst h W.hom))).obj
      (abelianEtaleFinal _)
  let bV := (MorphismProperty.Over.map ⊤
    (inferInstance : AlgebraicGeometry.Etale (pullback.fst h V.hom))).obj
      (abelianEtaleFinal _)
  let f : bV ⟶ bW := MorphismProperty.Over.homMk g (by
    change g ≫ (𝟙 _ ≫ pullback.fst h W.hom) = 𝟙 _ ≫ pullback.fst h V.hom
    rw [Category.id_comp, Category.id_comp]
    exact pullback.lift_fst _ _ _)
  have he : generatorArrow h V ≫ B.map v = f ≫ generatorArrow h W := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · simp only [Functor.id_obj, Functor.const_obj_obj, generatorArrow, Category.assoc,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.isoMk_hom_left,
        Iso.refl_hom, MorphismProperty.Over.pullback_map_left, Category.id_comp,
        limit.lift_π, PullbackCone.mk_π_app, pullbackSymmetry_hom_comp_fst_assoc,
        pullbackSymmetry_hom_comp_fst,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, B, f, g]
      erw [Category.id_comp (pullback.snd h W.hom)]
      exact (pullback.lift_snd _ _ _).symm
    · simp only [Functor.id_obj, Functor.const_obj_obj, generatorArrow, Category.assoc,
        MorphismProperty.Comma.comp_hom, Comma.comp_left, MorphismProperty.Over.isoMk_hom_left,
        Iso.refl_hom, MorphismProperty.Over.pullback_map_left, Category.id_comp,
        limit.lift_π, PullbackCone.mk_π_app, pullbackSymmetry_hom_comp_snd,
        MorphismProperty.Over.homMk_hom, Over.homMk_left, B, f, g]
      erw [Category.id_comp (pullback.fst h W.hom)]
      exact (pullback.lift_fst _ _ _).symm
  have hp := congrArg (fun k ↦ (U.obj A).obj.map k.op) he
  have hv := ConcreteCategory.congr_hom hp (abelianRepresentableHomEquiv W _
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app A))
  simpa only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply] using hv

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The universal section is compatible with a morphism of étale objects.
Source: Stacks Project, Tag 03Q8 (restriction on the cohomology presheaf), and
naturality of the free-sheaf, inverse-image, and constant-sheaf adjunctions.
(blueprint: lem-sbc-abelian-representable-generator-coherence).

Proof: Apply the constant-sheaf adjunction on T_V = Y ×_X V, evaluated at its
terminal étale object, to both sides. The constant pullback comparison sends
1 to 1. The generator for V is obtained by evaluating the h*-adjunction unit
on the identity of V. Mapping it by h*Z[v] gives the section corresponding to
v, by naturality of this unit and of the free/sheafification/Yoneda adjunction
in its representing object. The pullback of the generator for W also gives
this section: the map T_V to T_W is the base change of v. Conjugating with the
pullback symmetry and the final-object identifications in the definition of
the generator gives the same arrow over Y. The inverse-image composition
unit identity identifies the successive restriction comparisons with the
comparison for T_V to Y. Naturality of the localization restriction
isomorphism then supplies exactly the displayed upperStarComp component.
Both sides therefore classify the same section; injectivity of the adjunction
bijection proves equality. Only functoriality and terminal-object identities
are used, so identity v and empty fibre products require no extra hypotheses.
-/
theorem abelianRepresentableGenerator_coherence {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W V : X.Etale) (v : V ⟶ W) :
    let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
    let i := upperStarComp AddCommGrpCat.{u + 1} g (pullback.fst h W.hom)
      (pullback.fst h V.hom) (by simp [g])
    abelianRepresentableGenerator h V ≫
        (upperStar AddCommGrpCat.{u + 1} (pullback.fst h V.hom)).map
          ((upperStar AddCommGrpCat.{u + 1} h).map ((abelianRepresentable X).map v)) ≫
        i.hom.app ((upperStar AddCommGrpCat.{u + 1} h).obj
          ((abelianRepresentable X).obj W)) =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
          (AddCommGrpCat.of (ULift ℤ)) ≫
        (upperStar AddCommGrpCat.{u + 1} g).map (abelianRepresentableGenerator h W) := by
  dsimp only
  let g := pullback.map h V.hom h W.hom (𝟙 Y) v.left (𝟙 X) (by simp) (by simp)
  let rW := pullback.fst h W.hom
  let rV := pullback.fst h V.hom
  let i := upperStarComp AddCommGrpCat.{u + 1} g rW rV (by simp [g, rW, rV])
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)
  let C := (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj V)
  let a := (upperStar AddCommGrpCat.{u + 1} h).map ((abelianRepresentable X).map v)
  let bW := abelianEtaleFinal (pullback h W.hom)
  let bV := abelianEtaleFinal (pullback h V.hom)
  let adj := constantSheafAdj (pullback h V.hom).smallEtaleTopology
    AddCommGrpCat.{u + 1} (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale _)
  change abelianRepresentableGenerator h V ≫
    (upperStar AddCommGrpCat.{u + 1} rV).map a ≫ i.hom.app A =
      (Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1} g).inv.app
        (AddCommGrpCat.of (ULift ℤ)) ≫
          (upperStar AddCommGrpCat.{u + 1} g).map (abelianRepresentableGenerator h W)
  apply (cancel_mono (i.inv.app A)).1
  simp only [Category.assoc, Iso.hom_inv_id_app]
  erw [Category.comp_id ((upperStar AddCommGrpCat.{u + 1} rV).map a)]
  apply (adj.homEquiv _ _).injective
  apply (AddCommGrpCat.uliftZMultiplesAddEquiv _).injective
  symm
  refine (etaleSection_pullback rW rV g (by simp [g, rW, rV]) A
    (abelianRepresentableGenerator h W)).trans ?_
  symm
  rw [adj.homEquiv_naturality_right]
  change ((upperStar AddCommGrpCat.{u + 1} rV).map a).hom.app (op bV)
    (AddCommGrpCat.uliftZMultiplesAddEquiv _ (adj.homEquiv _ _
      (abelianRepresentableGenerator h V))) = _
  erw [generator_adjunct h V, generator_adjunct h W]
  rw [← ConcreteCategory.comp_apply]
  have hn := congrArg (fun f ↦ f.hom.app (op bV))
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} rV inferInstance).inv.naturality a)
  change _ ≫ _ = _ ≫ _ at hn
  rw [← hn, ConcreteCategory.comp_apply]
  erw [generatorSection_naturality h W V v]
  congr 2
  rw [← ConcreteCategory.comp_apply]
  have hc := congrArg (fun f ↦ f.hom.app (op bW))
    ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} rW inferInstance).inv_hom_id_app A)
  change _ ≫ _ = 𝟙 _ at hc
  rw [hc]
  rfl

end Etale
end AlgebraicGeometry
