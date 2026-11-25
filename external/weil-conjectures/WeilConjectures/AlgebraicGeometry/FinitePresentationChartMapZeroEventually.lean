/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.LocalOverlapTransitions
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.FinitePresentationZeroMapDescent
import WeilConjectures.AlgebraicGeometry.ModulePullbackFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # Eventual vanishing on a fixed affine cover chart

Source: Stacks Project, Tag 01ZR (3).
(blueprint: lem-pc-fp-chart-map-zero-eventually). -/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem map_zero_iff_natIso {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms C] [HasZeroMorphisms D]
    {P Q : C ⥤ D} (e : P ≅ Q) {M N : C} (δ : M ⟶ N) :
    P.map δ = 0 ↔ Q.map δ = 0 := by
  have hn := e.hom.naturality δ
  constructor
  · intro hz
    rw [hz, zero_comp] at hn
    apply (cancel_epi (e.hom.app M)).mp
    simpa using hn.symm
  · intro hz
    rw [hz, comp_zero] at hn
    apply (cancel_mono (e.hom.app N)).mp
    simpa using hn

private noncomputable def tensorNativeIso {X Y : Scheme.{u}} (g : X ⟶ Y) :
    Scheme.Modules.tensorPullback g ≅ Scheme.Modules.pullback g :=
  (Scheme.Modules.nonempty_tensorPullbackAdjunction g).some.leftAdjointUniq
    (Scheme.Modules.pullbackPushforwardAdjunction g)

private theorem native_comp_zero_iff {X Y Z : Scheme.{u}} (g : Z ⟶ Y) (f : Y ⟶ X)
    {M N : X.Modules} (δ : M ⟶ N) :
    (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback f).map δ) = 0 ↔
      (Scheme.Modules.pullback (g ≫ f)).map δ = 0 :=
  map_zero_iff_natIso (Scheme.Modules.pullbackComp g f) δ

private theorem native_iso_comp_zero_iff {X Y Z : Scheme.{u}} (e : Z ≅ Y)
    (f : Y ⟶ X) {M N : X.Modules} (δ : M ⟶ N) :
    (Scheme.Modules.pullback (e.hom ≫ f)).map δ = 0 ↔
      (Scheme.Modules.pullback f).map δ = 0 := by
  constructor
  · intro hz
    have hz' : (Scheme.Modules.pullback e.inv).map
        ((Scheme.Modules.pullback (e.hom ≫ f)).map δ) = 0 := by
      rw [hz, Functor.map_zero]
    have ht := (native_comp_zero_iff e.inv (e.hom ≫ f) δ).mp hz'
    have he : e.inv ≫ (e.hom ≫ f) = f := by
      rw [← Category.assoc, e.inv_hom_id, Category.id_comp]
    rw [he] at ht
    exact ht
  · intro hz
    apply (native_comp_zero_iff e.hom f δ).mp
    rw [hz, Functor.map_zero]

private theorem identity_model_zero_iff {W S Z : Scheme.{u}} (b : W ⟶ S)
    (t₀ : S ⟶ S) (t : Z ⟶ S) (ht : t ≫ t₀ = t) {V : Scheme.{u}} (q : V ⟶ W) (s : V ⟶ Z)
    (h : IsPullback q s b t) {F G : W.Modules} (δ : F ⟶ G) :
    (Scheme.Modules.moduleBaseChange b
      (T := Over.mk t₀) (T' := Over.mk t)
      (Over.homMk t ht)).map
        ((Scheme.Modules.tensorPullback (pullback.fst b t₀)).map δ) = 0 ↔
      (Scheme.Modules.pullback q).map δ = 0 := by
  let g := baseChangeMap b (Over.homMk t ht : Over.mk t ⟶ Over.mk t₀)
  let p := pullback.fst b t₀
  change (Scheme.Modules.tensorPullback g).map
    ((Scheme.Modules.tensorPullback p).map δ) = 0 ↔ _
  rw [map_zero_iff_natIso (tensorNativeIso g)]
  change (Scheme.Modules.tensorPullback p ⋙ Scheme.Modules.pullback g).map δ = 0 ↔ _
  rw [map_zero_iff_natIso (Functor.isoWhiskerRight (tensorNativeIso p)
    (Scheme.Modules.pullback g)) δ]
  change (Scheme.Modules.pullback g).map ((Scheme.Modules.pullback p).map δ) = 0 ↔ _
  rw [native_comp_zero_iff]
  have hp : g ≫ p = pullback.fst b t := by simp [g, p, baseChangeMap]
  rw [hp]
  have hq : h.isoPullback.hom ≫ pullback.fst b t = q := h.isoPullback_hom_fst
  rw [← hq, native_iso_comp_zero_iff]

-- The iterated chart pullbacks and tensor model comparisons need additional elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- A map on a base-changed affine chart, with finite type source and finitely
presented target, vanishes at some finite stage if it vanishes after pullback to the limit.
Source: Stacks Project, Tag 01ZR (3), applied to a single affine cover chart.
(blueprint: lem-pc-fp-chart-map-zero-eventually).

Proof: Write W for the chart at k and b : W → Spec(R_k) for its structural map.
The stage map X_k → X_j is affine, since it is a base change of a map between
spectra. Thus W, the inverse image of an affine chart of U, is affine, and b is
quasi-compact. Apply finitePresentation_zero_map_descent to b with both initial
indices equal to k. The pullback of b along the identity of Spec(R_k) is canonically
isomorphic to W; use this isomorphism to transport the two modules and the map.
The limit base change of W is canonically isomorphic to the chart pulled back
along overlapLimitMap: both are the iterated pullback of U.X a along the same
maps. The analogous comparison at every later stage identifies the base change
of the map with its pullback along overlapRefinementHom. These comparisons follow
by the pullback universal property (their two projections agree), and the induced
module comparisons follow from pullbackComp and pullbackCongr. The tensor pullback
used by moduleBaseChange and the native pullback are naturally isomorphic: both are
left adjoint to the same pushforward, so adjoint uniqueness supplies the comparison.
Naturality transports zero equations in both directions. Hence the given
limit-zero hypothesis is the hypothesis of zero-map descent, which gives l ≥ k.
No Noetherian, finite-cover,
finite-presentation-of-the-scheme or transition/coherence hypothesis is needed.
Zero modules and empty affine charts cause no exception to the argument. -/
theorem finitePresentation_chart_map_zero_eventually
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (U : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    [∀ a, IsAffine (U.X a)] (a : U.I₀) (k : I) (hjk : j ≤ k)
    (F G : ((U.pullback₁ (overlapStageMap R f hij hjk)).X a).Modules)
    (hF_ft : F.IsFiniteType) (hF_qc : F.IsQuasicoherent)
    (hG_fp : G.IsFinitePresentation) (hG_qc : G.IsQuasicoherent)
    (δ : F ⟶ G)
    (hδ : (Scheme.Modules.pullback
      (Scheme.Cover.pullbackHom (U.pullback₁ (overlapStageMap R f hij hjk))
        (overlapLimitMap R c f (hij.trans hjk)) a)).map δ = 0) :
    ∃ (l : I) (hkl : k ≤ l),
      (Scheme.Modules.pullback
        (overlapRefinementHom U (overlapStageMap R f hij hjk)
          (overlapStageMap R f hij (hjk.trans hkl))
          (overlapStageMap R f (hij.trans hjk) hkl)
          (overlapStageMap_comp R f hij hjk hkl) a)).map δ = 0 := by
  classical
  let V : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} :=
    U.pullback₁ (overlapStageMap R f hij hjk)
  let b := V.f a ≫ pullback.snd f (Spec.map (R.map (homOfLE (hij.trans hjk))))
  have hstage : IsAffineHom (overlapStageMap R f hij hjk) := by
    exact MorphismProperty.of_isPullback (isPullback_baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))).flip
      (show IsAffineHom (Spec.map (R.map (homOfLE hjk))) from inferInstance)
  have : IsAffine (V.X a) := by
    change IsAffine (pullback (overlapStageMap R f hij hjk) (U.f a))
    infer_instance
  have : QuasiCompact b := inferInstance
  let t₀ := Spec.map (R.map (homOfLE (le_refl k)))
  have hid : t₀ = 𝟙 (Spec (R.obj k)) := by
    dsimp [t₀]
    rw [R.map_id, Spec.map_id]
  let p := pullback.fst b t₀
  let P := Scheme.Modules.tensorPullback p
  let F₀ := P.obj F
  let G₀ := P.obj G
  let δ₀ := P.map δ
  have : F.IsFiniteType := hF_ft
  have : F.IsQuasicoherent := hF_qc
  have : G.IsFinitePresentation := hG_fp
  have : G.IsQuasicoherent := hG_qc
  have hF₀_ft : F₀.IsFiniteType :=
    (Scheme.Modules.tensorPullback_isFiniteType _ _ p F).1
  have hF₀_qc : F₀.IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent
      (pullback b t₀).ringCatSheaf).prop_of_iso
      ((tensorNativeIso p).app F).symm inferInstance
  have hG₀_fp : G₀.IsFinitePresentation := by
    exact Scheme.Modules.isFinitePresentation_of_iso ((tensorNativeIso p).app G).symm
  have hG₀_qc : G₀.IsQuasicoherent := by
    exact (SheafOfModules.isQuasicoherent
      (pullback b t₀).ringCatSheaf).prop_of_iso
      ((tensorNativeIso p).app G).symm inferInstance
  have hlim : IsPullback (Scheme.Cover.pullbackHom V
      (overlapLimitMap R c f (hij.trans hjk)) a)
      ((V.pullback₁ (overlapLimitMap R c f (hij.trans hjk))).f a ≫
        pullback.snd f (c.π.app (op i))) b (c.π.app (op k)) := by
    exact (IsPullback.of_hasPullback
      (overlapLimitMap R c f (hij.trans hjk)) (V.f a)).flip.paste_vert
      (isPullback_baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)))
  have hz := (identity_model_zero_iff b t₀ (c.π.app (op k))
    (by rw [hid, Category.comp_id]) _ _ hlim δ).mpr hδ
  have hd := finitePresentation_zero_map_descent R c hc k b k (le_refl k)
  obtain ⟨l, hkl, hl⟩ := hd F₀ G₀ hF₀_ft hF₀_qc hG₀_fp hG₀_qc δ₀ hz
  refine ⟨l, hkl, ?_⟩
  let r := overlapStageMap R f (hij.trans hjk) hkl
  let q := overlapStageMap R f hij hjk
  let q' := overlapStageMap R f hij (hjk.trans hkl)
  let e := overlapRefinementHom U q q' r (overlapStageMap_comp R f hij hjk hkl) a
  have hs : IsPullback e ((U.pullback₁ q').f a) (V.f a) r := by
    apply IsPullback.of_right _ (overlapRefinementHom_map U q q' r _ a)
      (IsPullback.of_hasPullback q (U.f a)).flip
    change IsPullback (e ≫ U.pullbackHom q a)
      ((U.pullback₁ q').f a) (U.f a) (r ≫ q)
    rw [overlapRefinementHom_comp]
    rw [show r ≫ q = q' from overlapStageMap_comp R f hij hjk hkl]
    exact (IsPullback.of_hasPullback q' (U.f a)).flip
  have hs' := hs.paste_vert (isPullback_baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (T' := Over.mk (Spec.map (R.map (homOfLE ((hij.trans hjk).trans hkl)))))
    (Over.homMk (Spec.map (R.map (homOfLE hkl)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
  exact (identity_model_zero_iff b t₀ (Spec.map (R.map (homOfLE hkl)))
    (by rw [hid, Category.comp_id]) _ _ hs' δ).mp hl

end AlgebraicGeometry
