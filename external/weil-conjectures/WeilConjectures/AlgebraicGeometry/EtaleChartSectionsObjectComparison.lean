/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Defs
import WeilConjectures.SixFunctors.Etale.LowerShriek.OpenImmersion.Defs
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
@[expose] public section
universe u
open CategoryTheory Limits Opposite
open scoped AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem restriction_unit
    (Λ : Type (u + 1)) [CommRing Λ] {T Y : Scheme.{u}} (f : T ⟶ Y) [Etale f]
    (F : Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (b : Y.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ f).obj b) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app F).hom.app (op b) ≫
        ((f)^*[ModuleCat.{u + 1} Λ].obj F).obj.map ψ.op ≫
        ((upperStarIsoLocalizationRestriction (ModuleCat.{u + 1} Λ) f inferInstance).hom.app
          F).hom.app (op c) =
      F.obj.map (((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ f inferInstance
        _root_.trivial).homEquiv c b).symm ψ).op := by
  let A := ModuleCat.{u + 1} Λ
  let ρ := (upperStarIsoLocalizationRestriction A f inferInstance).hom.app F
  have hu := congrArg (fun α ↦ α.hom.app (op b))
    (Adjunction.unit_leftAdjointUniq_hom_app (upperStarLowerStarAdjunction A f)
      (localizationRestrictionLowerStarAdjunction A f inferInstance) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at hu
  rw [ρ.hom.naturality, ← Category.assoc]
  erw [show ((upperStarLowerStarAdjunction A f).unit.app F).hom.app (op b) ≫
    ρ.hom.app (op ((MorphismProperty.Over.pullback @Etale ⊤ f).obj b)) =
    ((localizationRestrictionLowerStarAdjunction A f inferInstance).unit.app F).hom.app
      (op b) from hu]
  change (𝟙 _ ≫ F.obj.map _ ≫ 𝟙 _) ≫ F.obj.map _ = _
  simp only [Category.id_comp, Category.comp_id, ← Functor.map_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem composition_unit
    (Λ : Type (u + 1)) [CommRing Λ] {T Y R : Scheme.{u}}
    (f : T ⟶ Y) (g : Y ⟶ R) (t : T ⟶ R) (ht : t = f ≫ g)
    (F : Sheaf R.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (b : R.Etale) (c : T.Etale)
    (ψ : c ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj b) :
    ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) t).unit.app F).hom.app (op b) ≫
        ((t)^*[ModuleCat.{u + 1} Λ].obj F).obj.map ψ.op ≫
        ((upperStarComp (ModuleCat.{u + 1} Λ) f g t ht).hom.app F).hom.app (op c) =
      ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g).unit.app F).hom.app (op b) ≫
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app
          ((g)^*[ModuleCat.{u + 1} Λ].obj F)).hom.app
            (op ((MorphismProperty.Over.pullback @Etale ⊤ g).obj b)) ≫
        ((f)^*[ModuleCat.{u + 1} Λ].obj ((g)^*[ModuleCat.{u + 1} Λ].obj F)).obj.map
          (ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤) f g t ht).hom.app
            b).op := by
  let A := ModuleCat.{u + 1} Λ
  have h := congrArg (fun α ↦ α.hom.app (op b))
    (upperStarComp_hom_app_unit_app A f g F t ht)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    Adjunction.comp_unit_app, lowerStarComp,
    Functor.sheafPushforwardContinuousComp'_hom_app_hom_app] at h
  rw [((upperStarComp A f g t ht).hom.app F).hom.naturality, ← Category.assoc]
  erw [h]
  simp only [Functor.comp_obj, Iso.symm_inv, lowerStar_map_hom_app, Category.assoc,
    ← Functor.map_comp, ← op_comp]
  rfl

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The source and target arrows admit compatible object isomorphisms.
(blueprint: lem-sbc-etale-chart-sections-object-comparison)
Source: Stacks Project, Tag 0EZX, comparison of section objects.
The proof constructs the canonical inverse-image restriction and composition
isomorphisms and checks their compatibility with the two adjunction units. -/
theorem etaleChartSections_objectComparison
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (p : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    {V : S.Etale} {W : X.Etale}
    (φ : W ⟶ (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ p).obj V) :
    let a := Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) p).unit.app G).hom.app (op V) ≫
        ((p)^*[ModuleCat.{u + 1} Λ].obj G).obj.map φ.op)
    let b := Arrow.mk
      (((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ)
          (φ.left ≫ pullback.fst V.hom p)).unit.app
            ((V.hom)^*[ModuleCat.{u + 1} Λ].obj G)).hom.app
              (op (Scheme.Etale.mk (𝟙 V.left))))
    Nonempty (∃ (e₁ : a.left ≅ b.left) (e₂ : a.right ≅ b.right),
      e₁.hom ≫ b.hom = a.hom ≫ e₂.hom) := by
  classical
  let A := ModuleCat.{u + 1} Λ
  let j := W.hom
  let r := V.hom
  let q := φ.left ≫ pullback.fst V.hom p
  let t := j ≫ p
  have ht : t = q ≫ r := by
    dsimp [t, j, q, r]
    rw [Category.assoc, pullback.condition, ← Category.assoc]
    simpa using congrArg (· ≫ p) φ.w.symm
  let w : W.left.Etale := Scheme.Etale.mk (𝟙 W.left)
  let v : V.left.Etale := Scheme.Etale.mk (𝟙 V.left)
  let eW : (MorphismProperty.Over.map ⊤ (inferInstance : Etale j)).obj w ≅ W :=
    MorphismProperty.Over.isoMk (Iso.refl W.left) (by simp [w, j])
  let eV : (MorphismProperty.Over.map ⊤ (inferInstance : Etale r)).obj v ≅ V :=
    MorphismProperty.Over.isoMk (Iso.refl V.left) (by simp [v, r])
  let F := (p)^*[A].obj G
  let H := (r)^*[A].obj G
  let ρW := ((upperStarIsoLocalizationRestriction A j inferInstance).app F)
  let ρV := ((upperStarIsoLocalizationRestriction A r inferInstance).app G)
  let κ := ((upperStarComp A j p).symm ≪≫ upperStarComp A q r t ht).app G
  let z := (MorphismProperty.Over.pullback @Etale ⊤ q).obj v
  let : IsIso v.hom := inferInstanceAs (IsIso (𝟙 V.left))
  let ez : z ≅ w :=
    MorphismProperty.Over.isoMk (asIso (pullback.snd v.hom q)) (Category.comp_id _)
  let e₁ : G.obj.obj (op V) ≅ H.obj.obj (op v) :=
    G.obj.mapIso eV.op ≪≫ ((sheafSections _ A).obj (op v)).mapIso ρV.symm
  let e₂ : F.obj.obj (op W) ≅ ((q)^*[A].obj H).obj.obj (op z) :=
    F.obj.mapIso eW.op ≪≫ ((sheafSections _ A).obj (op w)).mapIso ρW.symm ≪≫
      ((sheafSections _ A).obj (op w)).mapIso κ ≪≫
        ((q)^*[A].obj H).obj.mapIso ez.op
  let δ : v ⟶ (MorphismProperty.Over.pullback @Etale ⊤ r).obj V :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 V.left) (𝟙 V.left) (by simp [r]))
      (by simp [v])
  let σ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ j).obj W :=
    MorphismProperty.Over.homMk (pullback.lift (𝟙 W.left) (𝟙 W.left) (by simp [j]))
      (by simp [w])
  let θ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ q).obj v := ez.inv
  let ψ : w ⟶ (MorphismProperty.Over.pullback @Etale ⊤ t).obj V :=
    MorphismProperty.Over.homMk
      (pullback.lift q (𝟙 W.left) (ht.symm.trans (Category.id_comp t).symm))
      (by simp [w])
  have hδ : ((upperStarLowerStarAdjunction A r).unit.app G).hom.app (op V) ≫
      H.obj.map δ.op = e₁.hom := by
    have h := restriction_unit Λ r G V v δ
    have hd : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ r inferInstance
        _root_.trivial).homEquiv v V).symm δ = eV.hom := by
      ext
      simp [δ, eV, Adjunction.homEquiv_counit]
    rw [hd] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op v)).mapIso ρV)).2 h
  have hσ : ((upperStarLowerStarAdjunction A j).unit.app F).hom.app (op W) ≫
      ((j)^*[A].obj F).obj.map σ.op =
        F.obj.map eW.hom.op ≫ ρW.inv.hom.app (op w) := by
    have h := restriction_unit Λ j F W w σ
    have hs : ((MorphismProperty.Over.mapPullbackAdj @Etale ⊤ j inferInstance
        _root_.trivial).homEquiv w W).symm σ = eW.hom := by
      ext
      simp [σ, eW, Adjunction.homEquiv_counit]
    rw [hs] at h
    exact (Iso.eq_comp_inv (((sheafSections _ A).obj (op w)).mapIso ρW)).2 h
  have hχj : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      j p t rfl).hom.app V =
      σ ≫ (MorphismProperty.Over.pullback @Etale ⊤ j).map φ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      j p t rfl).hom.app V).left =
        σ.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ j).map φ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : φ.left ≫ pullback.fst V.hom p =
            𝟙 W.left ≫ φ.left ≫ pullback.fst V.hom p by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, pullback.map_id, Category.id_comp, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst, limit.lift_π, PullbackCone.mk_π_app,
            limit.lift_π_assoc, cospan_left, t, ψ, q, σ]
          exact h
        exact (Category.id_comp _).symm
      · suffices h : 𝟙 W.left ≫ j = 𝟙 W.left ≫ φ.left ≫ pullback.snd V.hom p by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, pullback.map_id, Category.id_comp, Category.assoc,
            pullbackLeftPullbackSndIso_inv_fst_snd, limit.lift_π_assoc, cospan_right,
            PullbackCone.mk_π_app, limit.lift_π, cospan_left, t, ψ, q, σ]
          exact h
        have hw : j = φ.left ≫ pullback.snd V.hom p := by simpa using φ.w.symm
        exact (Category.id_comp _).trans (hw.trans (Category.id_comp _).symm)
    · simp [ψ, σ, t, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hθsnd : θ.left ≫ pullback.snd v.hom q = 𝟙 W.left := by
    have h : θ.left ≫ pullback.snd v.hom q = 𝟙 W.left ≫ 𝟙 W.left := θ.w
    exact h.trans (Category.id_comp _)
  have hθfst : θ.left ≫ pullback.fst v.hom q = q := by
    have h := congrArg (θ.left ≫ ·) (pullback.condition (f := v.hom) (g := q))
    change θ.left ≫ (pullback.fst v.hom q ≫ 𝟙 V.left) =
      θ.left ≫ (pullback.snd v.hom q ≫ q) at h
    erw [Category.comp_id, ← Category.assoc, hθsnd, Category.id_comp] at h
    exact h
  have hχq : ψ ≫ (MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      q r t ht).hom.app V =
      θ ≫ (MorphismProperty.Over.pullback @Etale ⊤ q).map δ := by
    apply MorphismProperty.Over.Hom.ext
    change ψ.left ≫ ((MorphismProperty.Over.pullbackComp (P := @Etale) (Q := ⊤)
      q r t ht).hom.app V).left =
        θ.left ≫ ((MorphismProperty.Over.pullback @Etale ⊤ q).map δ).left
    simp only [MorphismProperty.Over.pullbackComp_hom_app_left,
      MorphismProperty.Over.pullback_map_left]
    apply pullback.hom_ext
    · apply pullback.hom_ext
      · suffices h : q = θ.left ≫ pullback.fst v.hom q ≫ 𝟙 V.left by
          simp only [Functor.const_obj_obj, Functor.id_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst,
            limit.lift_π, PullbackCone.mk_π_app, Category.comp_id, ψ, δ]
          exact h
        exact (hθfst.symm).trans
          (congrArg (θ.left ≫ ·) (Category.comp_id _).symm)
      · suffices h : 𝟙 W.left ≫ q = θ.left ≫ pullback.fst v.hom q ≫ 𝟙 V.left by
          simp only [Functor.id_obj, Functor.const_obj_obj, MorphismProperty.Over.pullback,
            MorphismProperty.Over.mk, Functor.comp_obj, MorphismProperty.Over.homMk_hom,
            Over.homMk_left, Category.assoc, pullbackLeftPullbackSndIso_inv_fst_snd,
            limit.lift_π_assoc, cospan_right, PullbackCone.mk_π_app, Category.comp_id,
            limit.lift_π, ψ, δ]
          exact h
        exact (Category.id_comp _).trans ((hθfst.symm).trans
          (congrArg (θ.left ≫ ·) (Category.comp_id _).symm))
    · simp [ψ, hθsnd, MorphismProperty.Over.pullback, MorphismProperty.Over.mk]
  have hj := composition_unit Λ j p t rfl G V w ψ
  rw [hχj, op_comp, Functor.map_comp] at hj
  change _ = ((upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫
    ((upperStarLowerStarAdjunction A j).unit.app F).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ p).obj V)) ≫
    ((j)_*[A].obj ((j)^*[A].obj F)).obj.map φ.op ≫
    ((j)^*[A].obj F).obj.map σ.op at hj
  erw [← ((upperStarLowerStarAdjunction A j).unit.app F).hom.naturality_assoc] at hj
  erw [hσ] at hj
  have hq := composition_unit Λ q r t ht G V w ψ
  rw [hχq, op_comp, Functor.map_comp] at hq
  change _ = ((upperStarLowerStarAdjunction A r).unit.app G).hom.app (op V) ≫
    ((upperStarLowerStarAdjunction A q).unit.app H).hom.app
      (op ((MorphismProperty.Over.pullback @Etale ⊤ r).obj V)) ≫
    ((q)_*[A].obj ((q)^*[A].obj H)).obj.map δ.op ≫
    ((q)^*[A].obj H).obj.map θ.op at hq
  erw [← ((upperStarLowerStarAdjunction A q).unit.app H).hom.naturality_assoc] at hq
  erw [reassoc_of% hδ] at hq
  let Cj := ((sheafSections _ A).obj (op w)).mapIso ((upperStarComp A j p).app G)
  let Cq := ((sheafSections _ A).obj (op w)).mapIso ((upperStarComp A q r t ht).app G)
  have hj' :
      (((upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫ F.obj.map φ.op ≫
        F.obj.map eW.hom.op ≫ ρW.inv.hom.app (op w)) ≫ Cj.inv =
      ((upperStarLowerStarAdjunction A t).unit.app G).hom.app (op V) ≫
        ((t)^*[A].obj G).obj.map ψ.op :=
    (Iso.comp_inv_eq Cj).2 hj.symm
  have h := congrArg (· ≫ Cq.hom) hj'
  erw [Category.assoc, hq] at h
  refine ⟨⟨e₁, e₂, ?_⟩⟩
  change e₁.hom ≫ ((upperStarLowerStarAdjunction A q).unit.app H).hom.app (op v) =
    (((upperStarLowerStarAdjunction A p).unit.app G).hom.app (op V) ≫ F.obj.map φ.op) ≫
      e₂.hom
  apply (cancel_mono (((q)^*[A].obj H).obj.map θ.op)).mp
  dsimp [e₂, κ, Cj, Cq] at h ⊢
  simp only [Iso.op_hom] at h ⊢
  have hz : ((q)^*[A].obj H).obj.map ez.hom.op ≫
      ((q)^*[A].obj H).obj.map θ.op = 𝟙 _ :=
    (((q)^*[A].obj H).obj.mapIso ez.op).hom_inv_id
  simp only [Category.assoc] at h ⊢
  erw [hz, Category.comp_id]
  exact h.symm
end AlgebraicGeometry.Etale
