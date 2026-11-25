/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.AB
public import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence

/-!
# Étale restriction and pullback units

Source: Stacks Project, Sites, Tags 03CF and 03EF (unit-side counterpart).
(blueprint: lem-weil-pbc-etale-restriction-pullback-unit-eq)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- Pointwise form of the restriction comparison unit equation.
-- Adapted from the proved helper in EtaleChartSectionsObjectComparison.
private theorem restriction_unit
    {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj F).obj.map ψ.op ≫
        ((Etale.upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let A := AddCommGrpCat.{u + 1}
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
private theorem composition_unit
    {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology AddCommGrpCat.{u + 1})
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} t).unit.app F).hom.app (op b) ≫
        ((Etale.upperStar AddCommGrpCat.{u + 1} t).obj F).obj.map ψ.op ≫
        ((Etale.upperStarComp AddCommGrpCat.{u + 1} f g t ht).hom.app F).hom.app (op c) =
      ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} g).unit.app F).hom.app (op b) ≫
        ((Etale.upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((Etale.upperStar AddCommGrpCat.{u + 1} f).obj
          ((Etale.upperStar AddCommGrpCat.{u + 1} g).obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  let A := AddCommGrpCat.{u + 1}
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (Etale.upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, Etale.lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((Etale.upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, Etale.lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Unit compatibility for an étale object in a cartesian square.
Source: Stacks Project, Sites, Tags 03CF and 03EF (unit-side counterpart).
(blueprint: lem-weil-pbc-etale-restriction-pullback-unit-eq)

Proof (the node's five steps):
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
it to type the restriction comparison. The equality of abelian-group homomorphisms
is the displayed equality for every section a. The maps eW and eW' only remove
identity composites in the structure maps of the terminal étale objects.
-/
theorem etale_restriction_pullback_unit_eq
    {X Y W W' : Scheme.{u}}
    (g : Y ⟶ X) (p : W ⟶ X) (g' : W' ⟶ W) (p' : W' ⟶ Y)
    (hcomm : g' ≫ p = p' ≫ g)
    (ι : W' ⟶ pullback p g)
    (hι₁ : ι ≫ pullback.fst p g = g')
    (hι₂ : ι ≫ pullback.snd p g = p')
    [IsIso ι] [hp : Etale p] (hp' : Etale p') :
      let A := AddCommGrpCat.{u + 1}
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
  let A := AddCommGrpCat.{u + 1}
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
    have h := restriction_unit p F wx w delta
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ p inferInstance
        _root_.trivial).homEquiv w wx).symm delta = eW.hom := by
      ext
      simp [delta, eW, Adjunction.homEquiv_counit]
    rw [hd] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w)).mapIso rhoFIso)).2 h
  have hσ : ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.app (op wy') ≫
      ((Etale.upperStar A p').obj gF).obj.map sigma.op =
        gF.obj.map eW'.hom.op ≫ rhoGIso.inv.hom.app (op w') := by
    have h := restriction_unit p' gF wy' w' sigma
    have hs : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ p' inferInstance
        _root_.trivial).homEquiv w' wy').symm sigma = eW'.hom := by
      ext
      simp [sigma, eW', Adjunction.homEquiv_counit]
    rw [hs] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w')).mapIso rhoGIso)).2 h
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
  have hj := composition_unit p' g hbase hcomm F wx w' gamma
  rw [hχj, op_comp, Functor.map_comp] at hj
  change _ = ((Etale.upperStarLowerStarAdjunction A g).unit.app F).hom.app (op wx) ≫
    ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj wx)) ≫
    ((Etale.lowerStar A p').obj ((Etale.upperStar A p').obj gF)).obj.map iotaSite.op ≫
    ((Etale.upperStar A p').obj gF).obj.map sigma.op at hj
  erw [← ((Etale.upperStarLowerStarAdjunction A p').unit.app gF).hom.naturality_assoc] at hj
  erw [hσ] at hj
  have hq := composition_unit g' p hbase rfl F wx w' gamma
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
    (Iso.comp_inv_eq Cq).2 hq.symm
  have hh := congrArg (· ≫ Cj.hom) hq'
  erw [Category.assoc, hj] at hh
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

end AlgebraicGeometry
