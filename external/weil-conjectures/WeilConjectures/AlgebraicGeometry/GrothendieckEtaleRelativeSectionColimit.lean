/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.GrothendieckEtaleSectionSystemLaws
import WeilConjectures.SixFunctors.ProEtale.Comparison.Continuity
import WeilConjectures.SixFunctors.BaseChange.Pasting
import WeilConjectures.AlgebraicGeometry.GrothendieckAffineGlobalSectionColimit
import all WeilConjectures.AlgebraicGeometry.EtaleObjectSections
import Mathlib.CategoryTheory.Presentable.Directed
import WeilConjectures.AlgebraicGeometry.EtaleFiniteDataDescent
/-! # Degree-zero continuity on the qcqs étale basis -/
@[expose] public section
universe u' u v w t
open CategoryTheory Limits Opposite
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def finiteHypercoverColimit
    {C : Type u} [Category.{v} C] {A : Type w} [Category.{t} A]
    {J : Type*} [Category J] [HasColimitsOfShape J A]
    (P : J ⥤ Cᵒᵖ ⥤ A) (c : Cocone P) {U : C} (E : PreOneHypercover U)
    [PreservesLimitsOfShape (WalkingMulticospan E.multicospanShape)
      (colim : (J ⥤ A) ⥤ A)]
    (hE : IsLimit (E.multifork c.pt))
    (hP : ∀ j, IsLimit (E.multifork (P.obj j)))
    (h₀ : ∀ k, IsColimit (((evaluation _ A).obj (op (E.X k))).mapCocone c))
    (h₁ : ∀ {k l} (m : E.I₁ k l),
      IsColimit (((evaluation _ A).obj (op (E.Y m))).mapCocone c)) :
    IsColimit (((evaluation _ A).obj (op U)).mapCocone c) := by
  let B := (E.multicospanIndex P.flip).multicospan.flip
  let s : Cone B.flip := E.multifork P.flip
  have hs : IsLimit s := by
    refine evaluationJointlyReflectsLimits _ fun j ↦ ?_
    change IsLimit (((evaluation J A).obj j).mapCone (E.multifork P.flip))
    let e : (E.multicospanIndex P.flip).multicospan ⋙ (evaluation J A).obj j ≅
        (E.multicospanIndex (P.obj j)).multicospan :=
      NatIso.ofComponents (fun k ↦ by cases k <;> exact Iso.refl _) (by
        intro k l f
        cases f <;> simp)
    apply (IsLimit.postcomposeHomEquiv e _).1
    refine IsLimit.ofIsoLimit (hP j) (Cone.ext (Iso.refl _) ?_)
    intro k
    cases k with
    | left k =>
      change (P.obj j).map (E.f k).op =
        𝟙 _ ≫ ((P.obj j).map (E.f k).op ≫ 𝟙 _)
      simp only [Category.id_comp, Category.comp_id]
    | right k =>
      change (P.obj j).map (E.f k.1.1).op ≫ (P.obj j).map (E.p₁ k.2).op =
        𝟙 _ ≫ (((P.obj j).map (E.f k.1.1).op ≫ (P.obj j).map (E.p₁ k.2).op) ≫ 𝟙 _)
      simp only [Category.id_comp, Category.comp_id]
  let d : Cocone B :=
    { pt := (E.multicospanIndex c.pt).multicospan
      ι :=
        { app := fun j ↦
            { app := fun k ↦ match k with
                | .left k => (c.ι.app j).app (op (E.X k))
                | .right k => (c.ι.app j).app (op (E.Y k.2))
              naturality := by
                intro k l f
                cases f with
                | id k => simp
                | fst k => exact (c.ι.app j).naturality (E.p₁ k.2).op
                | snd k => exact (c.ι.app j).naturality (E.p₂ k.2).op }
          naturality := by
            intro i j f
            ext (k | k)
            · change (P.map f).app (op (E.X k)) ≫ _ = _ ≫ 𝟙 _
              simpa only [NatTrans.comp_app, Category.comp_id] using
                NatTrans.congr_app (c.w f) (op (E.X k))
            · change (P.map f).app (op (E.Y k.2)) ≫ _ = _ ≫ 𝟙 _
              simpa only [NatTrans.comp_app, Category.comp_id] using
                NatTrans.congr_app (c.w f) (op (E.Y k.2)) } }
  have hd : IsColimit d :=
    evaluationJointlyReflectsColimits _ fun k ↦ match k with
      | .left k => h₀ k
      | .right k => h₁ k.2
  let e : B.flip ⋙ colim ≅ d.pt :=
    (colimitIsoFlipCompColim B).symm ≪≫
      (colimit.isColimit B).coconePointUniqueUpToIso hd
  let r := (Cone.postcompose e.hom).obj (colim.mapCone s)
  have hr : IsLimit r :=
    (IsLimit.postcomposeHomEquiv e _).symm (isLimitOfPreserves colim hs)
  let φ := hr.conePointUniqueUpToIso hE
  refine IsColimit.ofIsoColimit (colimit.isColimit _) (Cocone.ext φ fun j ↦ ?_)
  apply hE.hom_ext
  intro k
  rw [Category.assoc, hr.conePointUniqueUpToIso_hom_comp hE k]
  simp only [r, e, Cone.postcompose_obj_π, NatTrans.comp_app, Functor.mapCone_π_app,
    colim_map, Iso.trans_hom, Iso.symm_hom, colimit.cocone_ι, ι_colimMap_assoc,
    colimitIsoFlipCompColim_inv_app, HasColimit.ι_isoOfNatIso_inv_assoc,
    compEvaluation_inv_app, Category.assoc]
  erw [Category.id_comp]
  have h := colimitObjIsoColimitCompEvaluation_ι_inv B j k
  have h' := congrArg (fun f ↦ f ≫
    ((colimit.isColimit B).coconePointUniqueUpToIso hd).hom.app k) h
  simp only [Category.assoc] at h'
  erw [h']
  rw [← NatTrans.comp_app, colimit.comp_coconePointUniqueUpToIso_hom]
  cases k with
  | left k => exact (c.ι.app j).naturality (E.f k).op
  | right k =>
    change ((P.obj j).map (E.f k.1.1).op ≫ (P.obj j).map (E.p₁ k.2).op) ≫
      (c.ι.app j).app (op (E.Y k.2)) =
      (c.ι.app j).app (op U) ≫ c.pt.map (E.f k.1.1).op ≫ c.pt.map (E.p₁ k.2).op
    simpa only [op_comp, Functor.map_comp, Category.assoc, Functor.const_obj_obj] using
      (c.ι.app j).naturality (E.p₁ k.2 ≫ E.f k.1.1).op


namespace AlgebraicGeometry
variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem c3_restriction_unit
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
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem c3_composition_unit
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
/-- Unit compatibility for an étale object in a cartesian square.
Source: Stacks Project, Sites, Tags 03CF and 03EF (unit-side counterpart).

Proof (the localization and composition unit equations):
1. Put h = g' ≫ p = p' ≫ g. Form P₀ = W ×ₓ W, P₁ = W ×ₓ Y, Q = W ×ₓ W'.
   The diagonal δ and the maps θ = (g',id), τ = (δg',id), σ = (ι,id) give
   φτ = φ'σ = γ = (g',id), for the two pullback-pasting isomorphisms φ, φ'.
   Use def-pc-fibre-product and lem-weil-pbc-inverse-image-composition (1).
2. The unit description and naturality of the restriction comparison in
   lem-weil-pbc-etale-inverse-image-restriction (2), restricted along δ, give
   (p⁻¹F)(δ)ηₚ(W) = ρF(W)⁻¹. Restricting the analogous formula along σ gives
   (p'⁻¹g⁻¹F)(σ)ηₚ'(P₁) = ρg⁻¹F(W')⁻¹(g⁻¹F)(ι).
3. Evaluate the unit equation of lem-weil-pbc-inverse-image-composition (2)
   for (p,g') at W and restrict along τ. Naturality of c and ηg', and step 2,
   identify the result with cₚ,g'(W')ηg'(W)ρF(W)⁻¹ = (h⁻¹F)(γ)ηh(W).
   The value of ηg'(W) here includes restriction along θ.
4. Apply the same composition unit equation for (g,p') and restrict along σ.
   The result is c_g,p'(W')ρg⁻¹F(W')⁻¹(g⁻¹F)(ι)ηg(W) = (h⁻¹F)(γ)ηh(W).
5. Equate steps 3 and 4, cancel c_g,p', and compose with the two restriction
   comparisons. Evaluating at any section gives the assertion. Étaleness of p'
   follows from base-change stability and the isomorphism ι, as in
   situation-conventions (1).

The existential proof hp' records the conclusion that p' is étale before using
it to type the restriction comparison. The conclusion is an equality of morphisms
in A, with no use of elements or concrete coefficients. The maps eW and eW' only remove
identity composites in the structure maps of the terminal étale objects.
-/
private theorem c3_etale_restriction_pullback_unit_eq
    {X Y W W' : Scheme.{u}}
    (g : Y ⟶ X) (p : W ⟶ X) (g' : W' ⟶ W) (p' : W' ⟶ Y)
    (hcomm : g' ≫ p = p' ≫ g)
    (ι : W' ⟶ pullback p g)
    (hι₁ : ι ≫ pullback.fst p g = g')
    (hι₂ : ι ≫ pullback.snd p g = p')
    [IsIso ι] [hp : Etale p] (hp' : Etale p') :
          let w : W.Etale := Scheme.Etale.mk (𝟙 W)
      let w' : W'.Etale := Scheme.Etale.mk (𝟙 W')
      let wx : X.Etale := Scheme.Etale.mk p
      let wy' : Y.Etale := @Scheme.Etale.mk _ _ p' hp'
      let eW : (MorphismProperty.Over.map ⊤ hp).obj w ≅ wx :=
        MorphismProperty.Over.isoMk (Iso.refl W) (by simp [wx, w])
      let eW' : (MorphismProperty.Over.map ⊤ hp').obj w' ≅ wy' :=
        MorphismProperty.Over.isoMk (Iso.refl W') (by simp [wy', w'])
      let theta : w' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g').obj w :=
        MorphismProperty.Over.homMk (pullback.lift g' (𝟙 W')
          (by exact (Category.comp_id g').trans (Category.id_comp g').symm))
          (by simp [w'])
      let iotaSite : wy' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj wx :=
        MorphismProperty.Over.homMk ι hι₂
      ∀ F : Sheaf X.smallEtaleTopology A,
        let pF := (Etale.upperStar A p).obj F
        let gF := (Etale.upperStar A g).obj F
        let K := (Etale.upperStar A g').obj pF
        let rhoF := (Etale.upperStarIsoLocalizationRestriction A p hp).hom.app F
        let rhoG := (Etale.upperStarIsoLocalizationRestriction A p' hp').hom.app gF
        let kappa := (Etale.upperStarComp A g' p).inv.app F ≫
          (Etale.upperStarComp A p' g (g' ≫ p) hcomm).hom.app F
        ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.app (op w) ≫
            K.obj.map theta.op ≫ kappa.hom.app (op w') ≫
            rhoG.hom.app (op w') ≫ gF.obj.map eW'.inv.op =
          rhoF.hom.app (op w) ≫ F.obj.map eW.inv.op ≫
            ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op wx) ≫
            gF.obj.map iotaSite.op := by
  let w : W.Etale := Scheme.Etale.mk (𝟙 W)
  let w' : W'.Etale := Scheme.Etale.mk (𝟙 W')
  let wx : X.Etale := Scheme.Etale.mk p
  let wy' : Y.Etale := @Scheme.Etale.mk _ _ p' hp'
  let eW : (MorphismProperty.Over.map ⊤ hp).obj w ≅ wx :=
    MorphismProperty.Over.isoMk (Iso.refl W) (by simp [wx, w])
  let eW' : (MorphismProperty.Over.map ⊤ hp').obj w' ≅ wy' :=
    MorphismProperty.Over.isoMk (Iso.refl W') (by simp [wy', w'])
  let theta : w' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g').obj w :=
    MorphismProperty.Over.homMk (pullback.lift g' (𝟙 W')
      (by exact (Category.comp_id g').trans (Category.id_comp g').symm))
      (by simp [w'])
  let iotaSite : wy' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ g).obj wx :=
    MorphismProperty.Over.homMk ι hι₂
  dsimp only
  intro F
  let pF := (Etale.upperStar A p).obj F
  let gF := (Etale.upperStar A g).obj F
  let K := (Etale.upperStar A g').obj pF
  let hbase := g' ≫ p
  let rhoFIso := (Etale.upperStarIsoLocalizationRestriction A p hp).app F
  let rhoGIso := (Etale.upperStarIsoLocalizationRestriction A p' hp').app gF
  have : Etale p' := hp'
  let delta : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p).obj wx :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W) (𝟙 W) (by simp [wx]))
      (by simp [w])
  let sigma : w' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ p').obj wy' :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W') (𝟙 W') (by simp [wy']))
      (by simp [w'])
  let gamma : w' ⟶ (MorphismProperty.Over.pullback @Etale ⊤ hbase).obj wx :=
    MorphismProperty.Over.homMk
      (pullback.lift g' (𝟙 W') (rfl.symm.trans (Category.id_comp hbase).symm))
      (by simp [w'])
  have hδ : ((Etale.upperStarLowerStarAdjunction A p).unit.app F).hom.app (op wx) ≫
      pF.obj.map delta.op = F.obj.map eW.hom.op ≫ rhoFIso.inv.hom.app (op w) := by
    have h := c3_restriction_unit A p F wx w delta
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ p inferInstance
        _root_.trivial).homEquiv w wx).symm delta = eW.hom := by
      ext
      simp [delta, eW, Adjunction.homEquiv_counit]
    rw [hd] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w)).mapIso rhoFIso)).2 (by
      simpa only [Category.assoc, Functor.mapIso_hom, sheafSections,
        Functor.flip_obj_map, ObjectProperty.ι_map, rhoFIso, pF,
        Iso.app_hom] using h)
  have hσ : ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.app (op wy') ≫
      ((Etale.upperStar A p').obj gF).obj.map sigma.op =
        gF.obj.map eW'.hom.op ≫ rhoGIso.inv.hom.app (op w') := by
    have h := c3_restriction_unit A p' gF wy' w' sigma
    have hs : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ p' inferInstance
        _root_.trivial).homEquiv w' wy').symm sigma = eW'.hom := by
      ext
      simp [sigma, eW', Adjunction.homEquiv_counit]
    rw [hs] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w')).mapIso rhoGIso)).2 (by
      simpa only [Category.assoc, Functor.mapIso_hom, sheafSections,
        Functor.flip_obj_map, ObjectProperty.ι_map, rhoGIso,
        Iso.app_hom] using h)
  have hχj : gamma ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      p' g hbase hcomm).hom.app wx =
      sigma ≫ (MorphismProperty.Over.pullback @Etale ⊤ p').map iotaSite := by
    apply MorphismProperty.Over.Hom.ext
    change gamma.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      p' g hbase hcomm).hom.app wx).left =
        sigma.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ p').map iotaSite).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : g' ≫ 𝟙 wx.left =
            𝟙 W' ≫ iotaSite.left ≫ pullback.fst wx.hom g by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst, limit.lift_π, PullbackCone.mk_π_app,
            limit.lift_π_assoc, cospan_left, hbase, gamma, sigma]
          exact h
        change g' ≫ 𝟙 W = 𝟙 W' ≫ ι ≫ pullback.fst p g
        simpa using hι₁.symm
      · suffices h : 𝟙 W' ≫ p' = 𝟙 W' ≫ iotaSite.left ≫ pullback.snd wx.hom g by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.id_comp, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst_snd, limit.lift_π_assoc, cospan_right,
            PullbackCone.mk_π_app, limit.lift_π, cospan_left, hbase, gamma, sigma]
          exact h
        have hw : p' = iotaSite.left ≫ pullback.snd wx.hom g := by simpa [wy'] using iotaSite.w.symm
        exact (Category.id_comp _).trans (hw.trans (Category.id_comp _).symm)
    · simp [gamma, sigma, hbase, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hθsnd : theta.left ≫ pullback.snd w.hom g' = 𝟙 W' := by
    have h : theta.left ≫ pullback.snd w.hom g' = 𝟙 W' ≫ 𝟙 W' := theta.w
    exact h.trans (Category.id_comp _)
  have hθfst : theta.left ≫ pullback.fst w.hom g' = g' := by
    have h := congrArg (theta.left ≫ ·) (pullback.condition (f := w.hom) (g := g'))
    change theta.left ≫ (pullback.fst w.hom g' ≫ 𝟙 W) =
      theta.left ≫ (pullback.snd w.hom g' ≫ g') at h
    erw [Category.comp_id, ← Category.assoc, hθsnd, Category.id_comp] at h
    exact h
  have hχq : gamma ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      g' p hbase rfl).hom.app wx =
      theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ g').map delta := by
    apply MorphismProperty.Over.Hom.ext
    change gamma.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      g' p hbase rfl).hom.app wx).left =
        theta.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ g').map delta).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : g' = theta.left ≫ pullback.fst w.hom g' ≫ 𝟙 W by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
            limit.lift_π, PullbackCone.mk_π_app, Category.comp_id, gamma, delta]
          exact h
        exact (hθfst.symm).trans
          (congrArg (theta.left ≫ ·) (Category.comp_id _).symm)
      · suffices h : 𝟙 W' ≫ g' = theta.left ≫ pullback.fst w.hom g' ≫ 𝟙 W by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
            limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
            limit.lift_π, gamma, delta]
          exact h
        exact (Category.id_comp _).trans ((hθfst.symm).trans
          (congrArg (theta.left ≫ ·) (Category.comp_id _).symm))
    · simp [gamma, hθsnd, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hj := c3_composition_unit A p' g hbase hcomm F wx w' gamma
  rw [hχj, op_comp, Functor.map_comp] at hj
  change _ = ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op wx) ≫
    ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj wx)) ≫
    ((Etale.lowerStar A p').obj ((Etale.upperStar A p').obj gF)).obj.map iotaSite.op ≫
    ((Etale.upperStar A p').obj gF).obj.map sigma.op at hj
  erw [← ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.naturality_assoc] at hj
  erw [hσ] at hj
  have hq := c3_composition_unit A g' p hbase rfl F wx w' gamma
  rw [hχq, op_comp, Functor.map_comp] at hq
  change _ = ((Etale.upperStarLowerStarAdjunction A p).unit.app F).hom.app (op wx) ≫
    ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj wx)) ≫
    ((Etale.lowerStar A g').obj ((Etale.upperStar A g').obj pF)).obj.map delta.op ≫
    ((Etale.upperStar A g').obj pF).obj.map theta.op at hq
  erw [← ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.naturality_assoc] at hq
  erw [reassoc_of% hδ] at hq
  let Cq := ((sheafSections _ A).obj (op w')).mapIso
    ((Etale.upperStarComp A g' p).app F)
  let Cj := ((sheafSections _ A).obj (op w')).mapIso
    ((Etale.upperStarComp A p' g hbase hcomm).app F)
  have hq' :
      (F.obj.map eW.hom.op ≫ rhoFIso.inv.hom.app (op w) ≫
        ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.app (op w) ≫
        K.obj.map theta.op) ≫ Cq.inv =
      ((Etale.upperStarLowerStarAdjunction A hbase).unit.app F).hom.app (op wx) ≫
        ((Etale.upperStar A hbase).obj F).obj.map gamma.op :=
    (Iso.comp_inv_eq Cq).2 (by simpa only [Category.assoc, Cq, Functor.mapIso_hom, sheafSections,
      Functor.flip_obj_map, ObjectProperty.ι_map, K, hbase,
      Iso.app_hom] using hq.symm)
  have hh := congrArg (· ≫ Cj.hom) hq'
  change _ = (_ ≫ _) ≫
    ((Etale.upperStarComp A p' g hbase hcomm).hom.app F).hom.app (op w') at hh
  simp only [Category.assoc] at hh
  rw [hj] at hh
  have hh' := congrArg (fun z ↦
    (rhoFIso.hom.hom.app (op w) ≫ F.obj.map eW.inv.op) ≫ z ≫
      rhoGIso.hom.hom.app (op w') ≫ gF.obj.map eW'.inv.op) hh
  have hrF : rhoFIso.hom.hom.app (op w) ≫ rhoFIso.inv.hom.app (op w) = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.app (op w)) rhoFIso.hom_inv_id
  have hrG : rhoGIso.inv.hom.app (op w') ≫ rhoGIso.hom.hom.app (op w') = 𝟙 _ :=
    congrArg (fun f ↦ f.hom.app (op w')) rhoGIso.inv_hom_id
  have heF : F.obj.map eW.inv.op ≫ F.obj.map eW.hom.op = 𝟙 _ :=
    (F.obj.mapIso eW.op).inv_hom_id
  have heG : gF.obj.map eW'.hom.op ≫ gF.obj.map eW'.inv.op = 𝟙 _ :=
    (gF.obj.mapIso eW'.op).hom_inv_id
  simp only [Category.assoc] at hh'
  erw [reassoc_of% heF, reassoc_of% hrF, reassoc_of% hrG, heG,
    Category.comp_id] at hh'
  change ((Etale.upperStarLowerStarAdjunction A g').unit.app pF).hom.app (op w) ≫
      K.obj.map theta.op ≫ (Cq.inv ≫ Cj.hom) ≫
      rhoGIso.hom.hom.app (op w') ≫ gF.obj.map eW'.inv.op =
    rhoFIso.hom.hom.app (op w) ≫ F.obj.map eW.inv.op ≫
      ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op wx) ≫
      gF.obj.map iotaSite.op
  simp only [Category.assoc]
  exact hh'


namespace Etale
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- The natural evaluation/global-sections comparison for an étale object.
Source: Stacks Project, Tag 03S2. -/
private noncomputable def c3_etaleObjectSectionsIso {X : Scheme.{u}} (V : X.Etale) :
    (sheafSections X.smallEtaleTopology A).obj (op V) ≅
      upperStar A V.hom ⋙
        Sheaf.Γ V.left.smallEtaleTopology A := by
  let w : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale V.hom)).obj w ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [w])
  exact (sheafSections X.smallEtaleTopology A).mapIso eW.op ≪≫
    Functor.isoWhiskerRight (upperStarIsoLocalizationRestriction A V.hom inferInstance).symm
      ((sheafSections V.left.smallEtaleTopology A).obj (op w)) ≪≫
    Functor.isoWhiskerLeft (upperStar A V.hom)
      (Sheaf.ΓNatIsoSheafSections V.left.smallEtaleTopology A
        (MorphismProperty.Over.mkIdTerminal (P := @Etale) V.left)).symm

set_option maxRecDepth 2048 in
-- Comparing nested pullback and localization components needs extra elaboration heartbeats.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- Étale evaluation is compatible with the unit for an arbitrary base change.
Source: Stacks Project, Tags 03CF, 03EF and 03S2.

Proof: Write p = Vf.hom and q = Vg.hom. The lift i = pullback.lift m q hm'
identifies Vg with Vf ×_Y X: its inverse is obtained by composing the projection to Vf
with Vf's projection to W and pairing that with the projection to X; the two identities
follow by pullback extensionality, hm, hm' and g = h ≫ f. Thus i is an isomorphism.
Apply etale_restriction_pullback_unit to (h,p,m,q) and i. In that equality the
restriction comparisons rhoH and rho(h^*H) are invertible. Move them to the other
sides and compose with global-sections/terminal-evaluation comparisons. Their inverses,
together with the identity-object isomorphisms eW and eW', are precisely the two
c3_etaleObjectSectionsIso A components in this statement. The map theta is the inverse of
the terminal-object pullback isomorphism used in globalSectionsUpperStarMap: both maps
have projections m and the identity, so pullback extensionality identifies them.
The composite of the h-unit on Vf with restriction along i is the W-component of the
f-pushforward of that unit followed by lowerStarComp; this follows from its definition
by the canonical pullback-pasting isomorphism and uniqueness of the two projections.
Finally, naturality of terminal evaluation moves the comparison
(upperStarComp m p)^{-1} followed by upperStarComp q h past evaluation, giving exactly
the final Γ-map displayed here. No property of H or of h is used.
-/
private theorem c3_etaleObjectSections_baseChange {R X Y : Scheme.{u}} (W : R.Etale)
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f)
    (m : pullback W.hom g ⟶ pullback W.hom f)
    (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
    (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h)
    (H : Sheaf Y.smallEtaleTopology A) :
      let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
    let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
    (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
        (lowerStarComp A h f g w).hom.app _).hom.app (op W)) ≫
        (c3_etaleObjectSectionsIso A Vg).hom.app ((upperStar A h).obj H) =
      (c3_etaleObjectSectionsIso A Vf).hom.app H ≫
        globalSectionsUpperStarMap A m ((upperStar A Vf.hom).obj H) ≫
        (Sheaf.Γ Vg.left.smallEtaleTopology A).map
          ((upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
            (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H)  := by
  let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
  let i := pullback.lift m Vg.hom hm'
  let j : pullback Vf.hom h ⟶ Vg.left :=
    pullback.lift (pullback.fst Vf.hom h ≫ pullback.fst W.hom f)
      (pullback.snd Vf.hom h) (by
        simp only [w, Category.assoc, pullback.condition]
        exact (pullback.condition_assoc (f := Vf.hom) (g := h) f))
  have hi : IsIso i := by
    refine ⟨⟨j, ?_, ?_⟩⟩
    · apply pullback.hom_ext <;> simp [i, j, Vf, Vg, hm]
    · apply pullback.hom_ext
      · apply pullback.hom_ext
        · simp [i, j, Vf, Vg, hm]
        · simp [i, j, Vf, Vg, hm', pullback.condition]
      · simp [i, j, Vf, Vg]
  let _ : IsIso i := hi
  have hp' : Etale Vg.hom := inferInstance
  have huH := c3_etale_restriction_pullback_unit_eq A h Vf.hom m Vg.hom hm' i
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hp' H
  dsimp only at huH
  let F := (upperStar A Vf.hom).obj H
  let G := (upperStar A h).obj H
  let K := (upperStar A m).obj F
  let k := (upperStarComp A m Vf.hom (m ≫ Vf.hom) rfl).inv.app H ≫
    (upperStarComp A Vg.hom h (m ≫ Vf.hom) hm').hom.app H
  let wF : Vf.left.Etale := Scheme.Etale.mk (𝟙 Vf.left)
  let wG : Vg.left.Etale := Scheme.Etale.mk (𝟙 Vg.left)
  let eF : (MorphismProperty.Over.map ⊤ (inferInstance : Etale Vf.hom)).obj wF ≅ Vf :=
    MorphismProperty.Over.isoMk (Iso.refl Vf.left) (by simp [wF])
  let eG : (MorphismProperty.Over.map ⊤ hp').obj wG ≅ Vg :=
    MorphismProperty.Over.isoMk (Iso.refl Vg.left) (by simp [wG])
  let rF := (upperStarIsoLocalizationRestriction A Vf.hom inferInstance).app H
  let rG := (upperStarIsoLocalizationRestriction A Vg.hom hp').app G
  let tF := Sheaf.ΓNatIsoSheafSections Vf.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vf.left)
  let tG := Sheaf.ΓNatIsoSheafSections Vg.left.smallEtaleTopology A
    (MorphismProperty.Over.mkIdTerminal (P := @Etale) Vg.left)
  let theta : wG ⟶ (MorphismProperty.Over.pullback @Etale ⊤ m).obj wF :=
    MorphismProperty.Over.homMk (pullback.lift m (𝟙 Vg.left)
      ((Category.comp_id m).trans (Category.id_comp m).symm)) (by simp [wG])
  let b : Vg ⟶ (MorphismProperty.Over.pullback @Etale ⊤ h).obj Vf :=
    MorphismProperty.Over.homMk i (pullback.lift_snd _ _ _)
  have hbSite : (MorphismProperty.Over.pullbackComp
      (P := @Etale) (Q := ⊤) h f g w).hom.app W = b := by
    apply MorphismProperty.Over.Hom.ext
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · simp [b, i, Vf, Vg, hm]
      · simp [b, i, Vf, Vg, hm', pullback.condition]
    · simp [b, i, Vf, Vg]
  have hb : ((lowerStarComp A h f g w).hom.app G).hom.app (op W) =
      G.obj.map b.op := by
    simp only [lowerStarComp, Functor.sheafPushforwardContinuousComp'_hom_app_hom_app,
      Iso.symm_inv, hbSite]
  have ht : globalSectionsUpperStarMap A m F ≫ tG.hom.app K =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op := by
    let a : wF ⟶ ⊤_ Vf.left.Etale := terminal.from _
    let c : wG ⟶ ⊤_ Vg.left.Etale := terminal.from _
    have hG : (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
        K.ΓRes (op wG) = K.obj.map c.op := by
      erw [← Sheaf.ΓRes_map K c.op, ← terminalEvaluation_eq_res _ _ terminalIsTerminal K]
      simp only [Iso.inv_hom_id_app_assoc]
    have hterm : c ≫ (PreservesTerminal.iso m.Etale).inv =
        theta ≫ (MorphismProperty.Over.pullback @Etale ⊤ m).map a := by
      exact (terminalIsTerminal.isTerminalObj m.Etale).hom_ext _ _
    simp only [globalSectionsUpperStarMap, tF, tG, terminalEvaluation_eq_res,
      Category.assoc]
    change F.ΓRes (op (⊤_ Vf.left.Etale)) ≫
      ((upperStarLowerStarAdjunction A m).unit.app F).hom.app _ ≫
      K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫
      (Sheaf.ΓNatIsoSheafSections _ _ terminalIsTerminal).inv.app K ≫
      K.ΓRes (op wG) = _
    erw [hG]
    have hmaps : K.obj.map (PreservesTerminal.iso m.Etale).inv.op ≫ K.obj.map c.op =
        K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op ≫
          K.obj.map theta.op := by
      rw [← Functor.map_comp, ← op_comp, hterm, op_comp, Functor.map_comp]
    erw [hmaps]
    have hn := ((upperStarLowerStarAdjunction A m).unit.app F).hom.naturality a.op
    change F.obj.map a.op ≫ _ = _ ≫
      K.obj.map ((MorphismProperty.Over.pullback @Etale ⊤ m).map a).op at hn
    erw [← reassoc_of% hn]
    erw [← Sheaf.ΓRes_map F a.op]
    simp only [Category.assoc]
  have hEF : (c3_etaleObjectSectionsIso A Vf).hom.app H =
      H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ tF.inv.app F := by rfl
  have hEG : (c3_etaleObjectSectionsIso A Vg).hom.app G =
      G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
        tG.inv.app ((upperStar A Vg.hom).obj G) := by rfl
  change ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
      K.obj.map theta.op ≫ k.hom.app (op wG) ≫ rG.hom.hom.app (op wG) ≫
        G.obj.map eG.inv.op =
    rF.hom.hom.app (op wF) ≫ H.obj.map eF.inv.op ≫
      ((upperStarLowerStarAdjunction A h).unit.app H).hom.app (op Vf) ≫
        G.obj.map b.op at huH
  have hz := congrArg (fun a ↦ H.obj.map eF.hom.op ≫ rF.inv.hom.app (op wF) ≫ a ≫
    G.obj.map eG.hom.op ≫ rG.inv.hom.app (op wG) ≫
      tG.inv.app ((upperStar A Vg.hom).obj G)) huH
  have hrG : rG.hom.hom.app (op wG) ≫ rG.inv.hom.app (op wG) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.hom_inv_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have hrF : rF.inv.hom.app (op wF) ≫ rF.hom.hom.app (op wF) = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← ObjectProperty.FullSubcategory.comp_hom,
      Iso.inv_hom_id, ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app]
  have heG : G.obj.map eG.inv.op ≫ G.obj.map eG.hom.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.hom_inv_id, op_id]
    exact G.obj.map_id _
  have heF : H.obj.map eF.hom.op ≫ H.obj.map eF.inv.op = 𝟙 _ := by
    rw [← Functor.map_comp, ← op_comp, Iso.inv_hom_id, op_id]
    exact H.obj.map_id _
  simp only [Category.assoc] at hz
  rw [reassoc_of% heG, reassoc_of% hrG, reassoc_of% hrF, reassoc_of% heF] at hz
  change (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
    (lowerStarComp A h f g w).hom.app G).hom.app (op W)) ≫
    (c3_etaleObjectSectionsIso A Vg).hom.app G =
      (c3_etaleObjectSectionsIso A Vf).hom.app H ≫ globalSectionsUpperStarMap A m F ≫
        (Sheaf.Γ Vg.left.smallEtaleTopology A).map k
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, lowerStar_map_hom_app, hb]
  rw [hEF, hEG]
  have hn := tG.inv.naturality k
  change k.hom.app (op wG) ≫ tG.inv.app _ = tG.inv.app K ≫
    (Sheaf.Γ Vg.left.smallEtaleTopology A).map k at hn
  have ht' : globalSectionsUpperStarMap A m F =
      tF.hom.app F ≫ ((upperStarLowerStarAdjunction A m).unit.app F).hom.app (op wF) ≫
        K.obj.map theta.op ≫ tG.inv.app K := by
    apply (cancel_mono (tG.hom.app K)).1
    simp only [Category.assoc]
    erw [Iso.inv_hom_id_app]
    erw [Category.comp_id]
    exact ht
  rw [ht']
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
  erw [← hn]
  exact hz.symm


private noncomputable def c3_pullbackSectionsIso {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology A) (W : R.Etale) (f : X ⟶ R) :
    ((lowerStar A f).obj ((upperStar A f).obj G)).obj.obj (op W) ≅
      (Sheaf.Γ (pullback W.hom f).smallEtaleTopology A).obj
        ((upperStar A (pullback.fst W.hom f ≫ W.hom)).obj G) :=
  (c3_etaleObjectSectionsIso A (f.Etale.obj W)).app ((upperStar A f).obj G) ≪≫
    (Sheaf.Γ (pullback W.hom f).smallEtaleTopology A).mapIso
      ((upperStarComp A (pullback.snd W.hom f) f
        (pullback.fst W.hom f ≫ W.hom) pullback.condition).symm.app G)

private theorem c3_globalSections_naturality {X Y : Scheme.{u}} (f : Y ⟶ X)
    {B C : Sheaf X.smallEtaleTopology A} (g : B ⟶ C) :
    (Sheaf.Γ X.smallEtaleTopology A).map g ≫ globalSectionsUpperStarMap A f C =
      globalSectionsUpperStarMap A f B ≫
        (Sheaf.Γ Y.smallEtaleTopology A).map ((upperStar A f).map g) := by
  unfold globalSectionsUpperStarMap
  rw [Category.assoc, Category.assoc,
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology A
      terminalIsTerminal).hom.naturality_assoc g]
  have hn := (upperStarLowerStarAdjunction A f).unit.naturality g
  simp only [Functor.id_map] at hn
  rw [← Functor.map_comp_assoc, hn, Functor.map_comp]
  simp only [Category.assoc]
  rw [← (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      terminalIsTerminal).inv.naturality]
  congr 1
  congr 1
  have hu := ((upperStar A f).map g).hom.naturality
    (PreservesTerminal.iso (Scheme.Hom.Etale f)).inv.op
  simp only [Functor.comp_map, Functor.flip_obj_map, ObjectProperty.ι_map]
  erw [lowerStar_map_hom_app]
  simpa only [Category.assoc] using! congrArg (fun a ↦ a ≫
    (Sheaf.ΓNatIsoSheafSections Y.smallEtaleTopology A
      terminalIsTerminal).inv.app ((upperStar A f).obj C)) hu.symm

set_option linter.unusedVariables false in
-- Projection equality proofs are referenced only through proof-irrelevant arguments.
set_option maxRecDepth 4000 in
-- Nested inverse-image and global-section functors need extra elaboration reduction.
/-- Evaluation of f_* f^* G at an étale object W identifies naturally with the global
sections of the pullback of G to W ×_R X. This is a comparison for a single cartesian
square, independent of any limit or compactness hypotheses.
Source: Stacks Project, Tags 03S2, 03CF and 03EF.

Proof: By the definition of direct image, the source is (f^* G)(W ×_R X). Restriction
along the étale second projection identifies this with Γ(W ×_R X, p^* f^* G), using the
étale inverse-image/restriction isomorphism and evaluation at the terminal object.
Compose with the inverse-image composition isomorphism and the equality
p ≫ f = fst ≫ W.hom to obtain the displayed isomorphism in A. For a cartesian map m,
apply the restriction/pullback-unit identity to the square over h. Naturality of the
restriction isomorphism moves the composition isomorphism past restriction. Naturality
of the unit moves the source composition isomorphism past pullback. Associativity of
inverse-image composition identifies the resulting composites. The two projection
equations specify the canonical cartesian map, so this proves the stated equality for
any m satisfying them. The argument uses only adjunctions and composition coherence. -/
private theorem c3_pullbackSections_comparison (R : Scheme.{u})
    (G : Sheaf R.smallEtaleTopology A) (W : R.Etale) :
    let v := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ pullback.fst W.hom f ≫ W.hom
    let F := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (upperStar A (v f)).obj G
    let e := fun {X : Scheme.{u}} (f : X ⟶ R) ↦ (c3_pullbackSectionsIso A G W f).hom
      ∀ {X Y : Scheme.{u}} (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R)
        (w : g = h ≫ f) (m : pullback W.hom g ⟶ pullback W.hom f)
        (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
        (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h),
        ((lowerStar A f).map
            ((upperStarLowerStarAdjunction A h).unit.app ((upperStar A f).obj G)) ≫
          (lowerStarComp A h f g w).hom.app _ ≫
          (lowerStar A g).map ((upperStarComp A h f g w).inv.app G)).hom.app (op W) ≫ e g =
        e f ≫ globalSectionsUpperStarMap A m (F f) ≫
          (Sheaf.Γ (pullback W.hom g).smallEtaleTopology A).map
            ((upperStarComp A m (v f) (v g)
              (by dsimp [v]; rw [← Category.assoc, hm])).inv.app G) := by
  dsimp
  intro X Y h f g w m hm hm'
  let Vf := (MorphismProperty.Over.pullback @Etale ⊤ f).obj W
  let Vg := (MorphismProperty.Over.pullback @Etale ⊤ g).obj W
  let H := (upperStar A f).obj G
  let d := (upperStarComp A h f g w).inv.app G
  let cf := (upperStarComp A Vf.hom f (pullback.fst W.hom f ≫ W.hom)
    pullback.condition).inv.app G
  let cg := (upperStarComp A Vg.hom g (pullback.fst W.hom g ≫ W.hom)
    pullback.condition).inv.app G
  let cm := (upperStarComp A m (pullback.fst W.hom f ≫ W.hom)
    (pullback.fst W.hom g ≫ W.hom)
    (by rw [← Category.assoc, hm])).inv.app G
  let Γg := Sheaf.Γ Vg.left.smallEtaleTopology A
  let Γf := Sheaf.Γ Vf.left.smallEtaleTopology A
  let ef := (c3_etaleObjectSectionsIso A Vf).hom.app H
  let eg := (c3_etaleObjectSectionsIso A Vg).hom.app ((upperStar A g).obj G)
  let rho := (((lowerStar A f).map ((upperStarLowerStarAdjunction A h).unit.app H) ≫
    (lowerStarComp A h f g w).hom.app _).hom.app (op W))
  suffices heq :
      ((rho ≫ ((lowerStar A g).map d).hom.app (op W)) ≫ eg ≫ Γg.map cg) =
        ((ef ≫ Γf.map cf) ≫ globalSectionsUpperStarMap A m _ ≫ Γg.map cm) by
    simpa only [rho, ef, eg, cf, cg, Γf, Γg, c3_pullbackSectionsIso,
      Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom,
      ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, Category.assoc,
      H, d, cm, Vf, Vg, Scheme.Hom.Etale, Functor.id_obj,
      MorphismProperty.Over.pullback, MorphismProperty.Over.mk, Functor.comp_obj]
      using heq
  have hn := (c3_etaleObjectSectionsIso A Vg).hom.naturality d
  change ((lowerStar A g).map d).hom.app (op W) ≫ eg =
    (c3_etaleObjectSectionsIso A Vg).hom.app ((upperStar A h).obj H) ≫
      Γg.map ((upperStar A Vg.hom).map d) at hn
  have hb := c3_etaleObjectSections_baseChange A W h f g w m hm hm' H
  let b := m ≫ Vf.hom
  let c₁ := upperStarComp A m Vf.hom b rfl
  let c₂ := upperStarComp A Vg.hom h b hm'
  change rho ≫ (c3_etaleObjectSectionsIso A Vg).hom.app ((upperStar A h).obj H) =
    ef ≫ globalSectionsUpperStarMap A m _ ≫ Γg.map (c₁.inv.app H ≫ c₂.hom.app H) at hb
  have hc : c₂.hom.app H ≫ (upperStar A Vg.hom).map d ≫ cg =
      c₁.hom.app H ≫ (upperStar A m).map cf ≫ cm := by
    have hbf : pullback.fst W.hom g ≫ W.hom = b ≫ f := by
      change pullback.fst W.hom g ≫ W.hom = (m ≫ pullback.snd W.hom f) ≫ f
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, hm]
    have h₁ := upperStarComp_hom_app_map_upperStarComp_inv_app A
      Vg.hom h f b g (pullback.fst W.hom g ≫ W.hom) hm' w hbf G
    have h₂ := upperStarComp_hom_app_map_upperStarComp_inv_app A
      m Vf.hom f b (pullback.fst W.hom f ≫ W.hom)
      (pullback.fst W.hom g ≫ W.hom) rfl pullback.condition hbf G
    dsimp [d, cf, cg, cm, c₁, c₂, H]
    rw [← Category.assoc, h₁, ← Category.assoc, h₂]
    simp
  rw [Category.assoc, reassoc_of% hn, ← Category.assoc, hb]
  simp only [Γg.map_comp, Category.assoc]
  rw [← Γg.map_comp, ← Γg.map_comp, ← Γg.map_comp, hc]
  simp only [Iso.inv_hom_id_app_assoc, Γg.map_comp]
  have hg := c3_globalSections_naturality A m cf
  change Γf.map cf ≫ globalSectionsUpperStarMap A m _ =
    globalSectionsUpperStarMap A m _ ≫ Γg.map ((upperStar A m).map cf) at hg
  rw [reassoc_of% hg]



set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem c3_rebaseSectionTransition {R S X Y : Scheme.{u}}
    (u : S ⟶ R) (f : Y ⟶ S) (g : X ⟶ S) (m : X ⟶ Y) (w : g = m ≫ f)
    (G : Sheaf R.smallEtaleTopology A) :
    globalSectionsUpperStarMap A m ((upperStar A (f ≫ u)).obj G) ≫
      (Sheaf.Γ X.smallEtaleTopology A).map
        ((upperStarComp A m (f ≫ u) (g ≫ u)
          (by rw [w, Category.assoc])).inv.app G) ≫
      (Sheaf.Γ X.smallEtaleTopology A).map ((upperStarComp A g u).hom.app G) =
    (Sheaf.Γ Y.smallEtaleTopology A).map ((upperStarComp A f u).hom.app G) ≫
      globalSectionsUpperStarMap A m ((upperStar A f).obj ((upperStar A u).obj G)) ≫
      (Sheaf.Γ X.smallEtaleTopology A).map
        ((upperStarComp A m f g w).inv.app ((upperStar A u).obj G)) := by
  have hn := c3_globalSections_naturality A m ((upperStarComp A f u).hom.app G)
  rw [reassoc_of% hn]
  simp only [← Functor.map_comp]
  congr 1
  congr 1
  have he := upperStarComp_hom_app_map_upperStarComp_inv_app A
    m f u g (f ≫ u) (g ≫ u) w rfl rfl G
  have hi := IsIso.inv_eq_inv.mpr he
  simpa only [IsIso.inv_comp, IsIso.inv_inv, ← Functor.map_inv,
    NatIso.inv_hom_app, NatIso.inv_inv_app] using hi.symm

private theorem c3_affine_globalSections_limit_isColimit
    {J : Type u} [SmallCategory J] [IsCofiltered J] {S : Scheme.{u}}
    [IsAffine S]
    (D : J ⥤ Scheme.{u}) [∀ j, IsAffine (D.obj j)]
    (π : D ⟶ (Functor.const J).obj S) (c : Cone D) (hc : IsLimit c)
    (p : c.pt ⟶ S) (hp : ∀ j, p = c.π.app j ≫ π.app j)
    (G : Sheaf S.smallEtaleTopology A) (H : Jᵒᵖ ⥤ A)
    (e : ∀ j, H.obj (op j) ≅ (Sheaf.Γ (D.obj j).smallEtaleTopology A).obj
      ((upperStar A (π.app j)).obj G))
    (hH : ∀ (j k : J) (f : j ⟶ k), H.map f.op ≫ (e j).hom =
      (e k).hom ≫ globalSectionsUpperStarMap A (D.map f)
        ((upperStar A (π.app k)).obj G) ≫
      (Sheaf.Γ (D.obj j).smallEtaleTopology A).map
        ((upperStarComp A (D.map f) (π.app k) (π.app j)
          (by simpa only [Functor.const_obj_obj, Functor.const_obj_map,
            Category.comp_id] using (π.naturality f).symm)).inv.app G))
    (K : Cocone H) (eK : K.pt ≅ (Sheaf.Γ c.pt.smallEtaleTopology A).obj
      ((upperStar A p).obj G))
    (hK : ∀ j, K.ι.app (op j) ≫ eK.hom =
      (e j).hom ≫ globalSectionsUpperStarMap A (c.π.app j)
        ((upperStar A (π.app j)).obj G) ≫
      (Sheaf.Γ c.pt.smallEtaleTopology A).map
        ((upperStarComp A (c.π.app j) (π.app j) p (hp j)).inv.app G)) :
    Nonempty (IsColimit K) := by
  obtain ⟨I, hI, hdir, hne, R, hR⟩ := IsFiltered.exists_directed Jᵒᵖ
  let D' := R.leftOp ⋙ D
  let (j : Iᵒᵖ) : IsAffine (D'.obj j) :=
    inferInstanceAs (IsAffine (D.obj (R.obj j.unop).unop))
  let c' := c.whisker R.leftOp
  have hc' : IsLimit c' := (Functor.Initial.isLimitWhiskerEquiv R.leftOp c).symm hc
  let π' : D' ⟶ (Functor.const Iᵒᵖ).obj S := Functor.whiskerLeft R.leftOp π
  let H' := R ⋙ H
  let K' := K.whisker R
  suffices h : Nonempty (IsColimit K') from
    h.map (Functor.Final.isColimitWhiskerEquiv R K)
  apply affine_globalSections_limit_isColimit_of_directed A D' π' c' hc' p
    (fun j ↦ hp (R.obj j).unop) G H' (fun j ↦ e (R.obj j).unop) ?_ K' eK ?_
  · intro j k f
    simpa only [H', D', π', Functor.comp_map, Functor.leftOp_map,
      Quiver.Hom.op_unop, Quiver.Hom.unop_op, Functor.comp_obj, Opposite.op_unop,
      Functor.whiskerLeft_app, Functor.leftOp_obj] using
      hH (R.obj k).unop (R.obj j).unop (R.map f).unop
  · intro j
    simpa only [K', H', c', π', Functor.comp_obj, Cocone.whisker_ι, Cone.whisker_π,
      Cone.whisker_pt,
      Opposite.op_unop, Functor.whiskerLeft_app, Functor.leftOp_obj] using
      hK (R.obj j).unop

private theorem c3_grothMap_eq {R S T : Scheme.{u}}
    (h : T ⟶ S) (f : S ⟶ R) (g : T ⟶ R) (w : g = h ≫ f)
    (G : Sheaf R.smallEtaleTopology A) (U : R.Etale) :
    (grothendieckRelativeSectionMap A h f g w.symm G).app (op U) =
      ((lowerStar A f).map
          ((upperStarLowerStarAdjunction A h).unit.app ((upperStar A f).obj G)) ≫
        (lowerStarComp A h f g w).hom.app _ ≫
        (lowerStar A g).map ((upperStarComp A h f g w).inv.app G)).hom.app (op U) := by
  simp only [grothendieckRelativeSectionMap, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.op_app,
    ObjectProperty.FullSubcategory.comp_hom, lowerStar_map_hom_app,
    lowerStarComp_hom_app_hom_app]
  rw [← ((upperStarComp A h f g w).inv.app G).hom.naturality]
  rfl

private noncomputable def c3_rebasedPullbackSectionsIso {R X : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology A) (W : R.Etale) (f : X ⟶ R) :
    ((lowerStar A f).obj ((upperStar A f).obj G)).obj.obj (op W) ≅
      (Sheaf.Γ (pullback W.hom f).smallEtaleTopology A).obj
        ((upperStar A (pullback.fst W.hom f)).obj ((upperStar A W.hom).obj G)) :=
  c3_pullbackSectionsIso A G W f ≪≫
    (Sheaf.Γ (pullback W.hom f).smallEtaleTopology A).mapIso
      ((upperStarComp A (pullback.fst W.hom f) W.hom).app G)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem c3_rebasedPullbackSections_comparison {R X Y : Scheme.{u}}
    (G : Sheaf R.smallEtaleTopology A) (W : R.Etale)
    (h : X ⟶ Y) (f : Y ⟶ R) (g : X ⟶ R) (w : g = h ≫ f)
    (m : pullback W.hom g ⟶ pullback W.hom f)
    (hm : m ≫ pullback.fst W.hom f = pullback.fst W.hom g)
    (hm' : m ≫ pullback.snd W.hom f = pullback.snd W.hom g ≫ h) :
    (grothendieckRelativeSectionMap A h f g w.symm G).app (op W) ≫
        (c3_rebasedPullbackSectionsIso A G W g).hom =
      (c3_rebasedPullbackSectionsIso A G W f).hom ≫
        globalSectionsUpperStarMap A m
          ((upperStar A (pullback.fst W.hom f)).obj ((upperStar A W.hom).obj G)) ≫
        (Sheaf.Γ (pullback W.hom g).smallEtaleTopology A).map
          ((upperStarComp A m (pullback.fst W.hom f) (pullback.fst W.hom g)
            hm.symm).inv.app ((upperStar A W.hom).obj G)) := by
  simp only [c3_rebasedPullbackSectionsIso, Iso.trans_hom, Functor.mapIso_hom]
  rw [← Category.assoc, c3_grothMap_eq A h f g w G W,
    c3_pullbackSections_comparison A R G W h f g w m hm hm']
  simp only [Category.assoc, Iso.app_hom]
  rw [c3_rebaseSectionTransition A W.hom (pullback.fst W.hom f)
    (pullback.fst W.hom g) m hm.symm G]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Canonical relative section cocones are colimiting on affine étale objects.
Source: Stacks Project, Étale Cohomology, Tag 09YQ in degree zero, and
Sites, Tag 0738(4); blueprint étale cohomology continuity, detailed proof paragraph 2.

Proof: restrict to the cofiltered over category of i; its forgetful functor is initial.
Pull back the whole limiting cone along the affine etale object U. Connected pullback
pasting gives a limit cone with stages U times D_j, and the affine transition maps
make every one of these stages affine. Etale localization identifies evaluation of
the relative section presheaf at U with global sections of the pullback to U times D_j.
The same identification at the cone point intertwines the maps: prove the localization
unit equation from uniqueness of adjoints, then combine it with inverse-image composition
coherence. Rebase the coefficient sheaf along U.hom by the composition associativity
equation, so the fixed base is the affine scheme U itself. Reindex this affine system
by a coinitial directed preorder, apply
`affine_globalSections_limit_isColimit_of_directed`, and reflect the resulting colimit
through final reindexing. All objects and isomorphisms in this reduction are constructed
explicitly. -/
private theorem affineRelativeSectionColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (i : I) (G : Sheaf (D.obj i).smallEtaleTopology A)
    (U : (D.obj i).Etale) [IsAffine U.left] :
    Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
      (relativeSectionCocone A D c i G))) := by
  classical
  let : IsConnected (Over i) := IsCofiltered.isConnected (Over i)
  let B : Over i ⥤ Scheme.{u} := Over.forget i ⋙ D
  let π : B ⟶ (Functor.const (Over i)).obj (D.obj i) :=
    { app := fun j ↦ D.map j.hom
      naturality := fun j k a ↦ by
        change D.map a.left ≫ D.map k.hom = D.map j.hom ≫ 𝟙 _
        rw [← D.map_comp, Over.w a, Category.comp_id] }
  let c' : Cone B := c.whisker (Over.forget i)
  have hc' : IsLimit c' :=
    (Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc
  let E : Over i ⥤ Scheme.{u} :=
    { obj := fun j ↦ pullback U.hom (π.app j)
      map := fun {j k} a ↦ pullback.map _ _ _ _ (𝟙 U.left) (B.map a) (𝟙 _)
        (by simp) (by
          have h := π.naturality a
          change B.map a ≫ π.app k = π.app j ≫ 𝟙 _ at h
          exact (Category.comp_id _).symm.trans h.symm)
      map_id := fun j ↦ by apply pullback.hom_ext <;> simp
      map_comp := fun f g ↦ by apply pullback.hom_ext <;> simp }
  let d : Cone E :=
    { pt := pullback U.hom (c.π.app i)
      π :=
        { app := fun j ↦ pullback.map _ _ _ _ (𝟙 U.left) (c'.π.app j) (𝟙 _)
            (by simp) (by simp [c', π])
          naturality := fun j k f ↦ by apply pullback.hom_ext <;> simp [E] } }
  let β : E ⟶ B :=
    { app := fun j ↦ pullback.snd U.hom (π.app j)
      naturality := fun j k f ↦ by simp [E] }
  have hd : IsLimit d :=
    isLimitOfIsPullbackOfIsConnected β d c'
      { hom := pullback.snd U.hom (c.π.app i)
        w := fun j ↦ by simp [d, β] }
      (fun j ↦ isPullback_pullback_map U.hom (c.π.app i) (π.app j)
        (c'.π.app j) (by simp [c', π])) hc'
  have (j : Over i) : IsAffine (E.obj j) := by
    change IsAffine (pullback U.hom (D.map j.hom))
    have hmap : IsAffineHom (D.map j.hom) := inferInstance
    let : IsAffineHom (pullback.fst U.hom (D.map j.hom)) :=
      MorphismProperty.pullback_fst _ _ hmap
    exact @isAffine_of_isAffineHom _ _ (pullback.fst U.hom (D.map j.hom))
      inferInstance ‹IsAffine U.left›
  let σ : E ⟶ (Functor.const (Over i)).obj U.left :=
    { app := fun j ↦ pullback.fst U.hom (π.app j)
      naturality := fun j k f ↦ by simp [E] }
  let Q : d.pt ⟶ U.left := pullback.fst U.hom (c.π.app i)
  have hQ : ∀ j, Q = d.π.app j ≫ σ.app j := by
    intro j
    simp [Q, d, σ]
  let H := relativeSectionDiagram A D i G ⋙ (evaluation _ A).obj (op U)
  let K := ((evaluation _ A).obj (op U)).mapCocone (relativeSectionCocone A D c i G)
  apply c3_affine_globalSections_limit_isColimit A E σ d hd Q hQ
    ((upperStar A U.hom).obj G) H
    (fun j ↦ c3_rebasedPullbackSectionsIso A G U (D.map j.hom)) ?_ K
    (c3_rebasedPullbackSectionsIso A G U (c.π.app i)) ?_
  · intro j k f
    change (grothendieckRelativeSectionMap A (D.map f.left) (D.map k.hom)
      (D.map j.hom) (by rw [← D.map_comp, Over.w f]) G).app (op U) ≫ _ = _
    exact c3_rebasedPullbackSections_comparison A G U (D.map f.left)
      (D.map k.hom) (D.map j.hom) (by rw [← D.map_comp, Over.w f])
      (E.map f) (by simp [E, π]) (by simp [E, B, π])
  · intro j
    change (grothendieckRelativeSectionMap A (c.π.app j.left) (D.map j.hom)
      (c.π.app i) (c.w j.hom) G).app (op U) ≫ _ = _
    exact c3_rebasedPullbackSections_comparison A G U (c.π.app j.left)
      (D.map j.hom) (c.π.app i) (c.w j.hom).symm
      (d.π.app j) (by simp [d, π]) (by simp [d, c', π])

end Etale
end AlgebraicGeometry

namespace AlgebraicGeometry.Etale

private noncomputable def affineOpenPreOneHypercover {S : Scheme.{u}} (U : S.Etale)
    (d : ProEtale.AffineOpenCoverData U.left) : PreOneHypercover.{u} U where
  I₀ := d.ι₀
  X k := ProEtale.overOpens (P := @AlgebraicGeometry.Etale) (fun _ _ ↦ inferInstance) U (d.O k)
  f k := ProEtale.overOpensι (P := @AlgebraicGeometry.Etale)
    (fun _ _ ↦ inferInstance) U (d.O k)
  I₁ := d.ι₁
  Y k l m := ProEtale.overOpens (P := @AlgebraicGeometry.Etale)
    (fun _ _ ↦ inferInstance) U (d.W k l m)
  p₁ k l m := MorphismProperty.Over.homMk (Scheme.homOfLE _ (d.W_le_left m))
    (by simp [ProEtale.overOpens]) trivial
  p₂ k l m := MorphismProperty.Over.homMk (Scheme.homOfLE _ (d.W_le_right m))
    (by simp [ProEtale.overOpens]) trivial
  w k l m := MorphismProperty.Over.Hom.ext
    ((Scheme.homOfLE_ι _ (d.W_le_left m)).trans (Scheme.homOfLE_ι _ (d.W_le_right m)).symm)

private noncomputable def affineOpenOneHypercover {S : Scheme.{u}} (U : S.Etale)
    (d : ProEtale.AffineOpenCoverData U.left) : S.smallEtaleTopology.OneHypercover U :=
  ProEtale.oneHypercoverOfIsOpenImmersion (P := @AlgebraicGeometry.Etale)
    (fun _ _ ↦ inferInstance) S.smallEtaleTopology
    ProEtale.mem_smallEtaleTopology_of_isOpenImmersion (affineOpenPreOneHypercover U d)
    (fun k ↦ inferInstanceAs (IsOpenImmersion (d.O k).ι))
    (fun m ↦ inferInstanceAs (IsOpenImmersion (Scheme.homOfLE _ (d.W_le_left m))))
    (fun x ↦ by
      obtain ⟨k, hk⟩ := d.exists_mem_preimage (𝟙 U.left) x
      exact ⟨k, ⟨⟨x, hk⟩, rfl⟩⟩)
    (fun k l _ hk hl ↦ by
      obtain ⟨⟨x, hk⟩, rfl⟩ := hk
      obtain ⟨⟨y, hl⟩, rfl : y = x⟩ := hl
      obtain ⟨m, hm⟩ := d.exists_mem_preimage_W (𝟙 U.left) hk hl
      have hcomp : ((affineOpenPreOneHypercover U d).p₁ m).left ≫
          ((affineOpenPreOneHypercover U d).f k).left = (d.W k l m).ι :=
        Scheme.homOfLE_ι _ (d.W_le_left m)
      refine ⟨m, ?_⟩
      rw [hcomp]
      exact ⟨⟨y, hm⟩, rfl⟩)

private theorem affineOpenOneHypercoverFinite {S : Scheme.{u}} (U : S.Etale)
    (d : ProEtale.AffineOpenCoverData U.left) : (affineOpenOneHypercover U d).Finite where
  finite₀ := inferInstanceAs (Finite d.ι₀)
  finite₁ k l := inferInstanceAs (Finite (d.ι₁ k l))

attribute [local instance] affineOpenOneHypercoverFinite

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private noncomputable def qcqsColimitOfAffine
    {A : Type w} [Category.{u + 1} A] [Abelian A]
    [IsGrothendieckAbelian.{u + 1} A]
    {J : Type u} [SmallCategory J] [IsFiltered J]
    {S : Scheme.{u}} (P : J ⥤ S.Etaleᵒᵖ ⥤ A) (c : Cocone P)
    (hP : ∀ j, Presheaf.IsSheaf S.smallEtaleTopology (P.obj j))
    (hc : Presheaf.IsSheaf S.smallEtaleTopology c.pt)
    (ha : ∀ V : S.Etale, IsAffine V.left →
      Nonempty (IsColimit (((evaluation _ A).obj (op V)).mapCocone c)))
    (U : S.Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    IsColimit (((evaluation _ A).obj (op U)).mapCocone c) := by
  have : HasFilteredColimitsOfSize.{u, u} A :=
    hasFilteredColimitsOfSize_of_univLE.{u, u, u + 1, u + 1}
  have : AB5OfSize.{u, u} A := AB5OfSize_of_univLE.{u, u, u + 1, u + 1} A
  let d := (ProEtale.nonempty_affineOpenCoverData U.left).some
  let E := affineOpenOneHypercover U d
  have h₀ (k : E.I₀) : IsAffine (E.X k).left := d.isAffineOpen_O k
  have h₁ {k l : E.I₀} (m : E.I₁ k l) : IsAffine (E.Y m).left :=
    d.isAffineOpen_W k l m
  exact finiteHypercoverColimit P c E.toPreOneHypercover
    (E.isLimitMultifork ⟨c.pt, hc⟩)
    (fun j ↦ E.isLimitMultifork ⟨P.obj j, hP j⟩)
    (fun k ↦ (ha (E.X k) (h₀ k)).some)
    (fun m ↦ (ha (E.Y m) (h₁ m)).some)


variable (A : Type u') [Category.{u + 1} A] [Abelian A]
  [IsGrothendieckAbelian.{u + 1} A]

/-- Canonical relative section cocones are colimiting on qcqs étale objects.
Source: blueprint étale cohomology continuity, detailed proof paragraph 2;
Stacks Project, Étale Cohomology, Tag 09YQ, degree zero, and Sites, Tag 0738(4).
The categorical coefficient generalization is the finite-equalizer argument below.

Proof: choose a finite cover of U by affine opens and finite affine open covers of
its pairwise intersections. These form a finite one-hypercover, including when U is
empty. Apply the affine case to each degree-zero and degree-one component. The
multifork of a sheaf on this hypercover is a limit. AB5 commutes this finite matching
limit with the filtered colimit, and the colimit universal property identifies the
resulting cocone with evaluation at U. For the affine case, restrict the scheme
system to stages over i, pull the limiting cone back along U, and use connected
pullback pasting. All resulting stages are affine. Etale localization identifies
relative sections at U with global sections on these pullbacks. A proved unit and
composition calculation intertwines their transitions and cocone maps, including
the change of coefficient base to the affine object U itself. Finally reindex by a
coinitial directed preorder and use the affine global-section continuity
statement. Thus the qcqs gluing, arbitrary-index reindexing, and all normalization
calculations are proved here; the directed affine continuity core is the remaining
named obligation. No cohomology or resolution is used.
(auxiliary; not a blueprint node) -/
theorem relativeSectionCocone_isColimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
    [∀ i, CompactSpace (D.obj i)] [∀ i, QuasiSeparatedSpace (D.obj i)]
    [∀ {i j} (g : i ⟶ j), IsAffineHom (D.map g)]
    (c : Cone D) [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    (hc : IsLimit c) (i : I) (G : Sheaf (D.obj i).smallEtaleTopology A)
    (U : (D.obj i).Etale) [CompactSpace U.left] [QuasiSeparatedSpace U.left] :
    Nonempty (IsColimit (((evaluation _ A).obj (op U)).mapCocone
      (relativeSectionCocone A D c i G))) := by
  have hAffine (V : (D.obj i).Etale) (hV : IsAffine V.left) :=
    affineRelativeSectionColimit A D c hc i G V
  refine ⟨qcqsColimitOfAffine (relativeSectionDiagram A D i G)
    (relativeSectionCocone A D c i G) (fun j ↦ ?_) ?_ hAffine U⟩
  · exact ((lowerStar A (D.map j.unop.hom)).obj
      ((upperStar A (D.map j.unop.hom)).obj G)).property
  · exact ((lowerStar A (c.π.app i)).obj
      ((upperStar A (c.π.app i)).obj G)).property

end AlgebraicGeometry.Etale
