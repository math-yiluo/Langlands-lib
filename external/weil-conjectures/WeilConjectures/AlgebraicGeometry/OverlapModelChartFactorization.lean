/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OverlapConjugateRestriction
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso

@[expose] public section

universe u
open CategoryTheory
namespace AlgebraicGeometry
noncomputable section
attribute [local irreducible] Scheme.Modules.pullback Scheme.Modules.tensorPullback
  Scheme.Modules.tensorPullbackCompositionIso Adjunction.leftAdjointUniq
  Scheme.Modules.pullbackComp pullbackCompOfEq Scheme.Modules.pullbackCongr
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem pc_symm_app {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules) : (Scheme.Modules.pullbackComp f g).symm.app M =
      ((Scheme.Modules.pullbackComp f g).app M).symm := rfl

private theorem pc_def {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (a : Z ⟶ X) (ha : f ≫ g = a) (M : X.Modules) :
    pullbackCompOfEq f g a ha M = (Scheme.Modules.pullbackComp f g).app M ≪≫
      (Scheme.Modules.pullbackCongr ha).app M := by
  unfold pullbackCompOfEq
  rfl

private theorem pc_refl {X Y Z : Scheme.{u}} (f : Z ⟶ Y) (g : Y ⟶ X)
    (M : X.Modules) : pullbackCompOfEq f g (f ≫ g) rfl M =
      (Scheme.Modules.pullbackComp f g).app M := by
  unfold pullbackCompOfEq Scheme.Modules.pullbackCongr
  exact Iso.trans_refl _

private theorem pc_assoc
    {W X Y Z : Scheme.{u}} (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X)
    (a : W ⟶ Y) (b : Z ⟶ X) (c : W ⟶ X)
    (ha : f ≫ g = a) (hb : g ≫ h = b) (hc : a ≫ h = c)
    (hc' : f ≫ b = c) (M : X.Modules) :
    (Scheme.Modules.pullback f).map (pullbackCompOfEq g h b hb M).hom ≫
        (pullbackCompOfEq f b c hc' M).hom =
      (pullbackCompOfEq f g a ha ((Scheme.Modules.pullback h).obj M)).hom ≫
        (pullbackCompOfEq a h c hc M).hom := by
  subst a b c
  have ht := congrArg (fun t ↦ t.app M)
    (Scheme.Modules.pseudofunctor_associativity f g h)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Category.id_comp] at ht
  rw [pc_refl, pc_refl, pc_refl]
  unfold pullbackCompOfEq
  simp only [Iso.trans_hom, Iso.app_hom]
  rw [← cancel_epi ((Scheme.Modules.pullback f).map
    ((Scheme.Modules.pullbackComp g h).inv.app M)),
    ← cancel_epi ((Scheme.Modules.pullbackComp f (g ≫ h)).inv.app M)]
  simp only [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
  rw [(Scheme.Modules.pullback f).map_id]
  simp only [Category.id_comp, Iso.inv_hom_id_app_assoc]
  simpa only [Scheme.Modules.pullbackCongr, eqToIso.hom] using ht.symm

private theorem eta_mate {X Y : Scheme.{u}} (f : X ⟶ Y) :
    conjugateEquiv (Scheme.Modules.pullbackPushforwardAdjunction f)
      (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
      (overlapAdjunctionComparison f).hom = 𝟙 _ := by
  simp [overlapAdjunctionComparison, Adjunction.leftAdjointUniq,
    conjugateIsoEquiv]

private theorem tensor_compat {X Y Z : Scheme.{u}}
    (p : Z ⟶ Y) (q : Y ⟶ X) (t : Z ⟶ X) (h : p ≫ q = t) (F : X.Modules) :
    (Scheme.Modules.tensorPullbackCompositionIso p q t h).hom.app F ≫
        (overlapAdjunctionComparison p).hom.app
          ((Scheme.Modules.tensorPullback q).obj F) ≫
        (Scheme.Modules.pullback p).map ((overlapAdjunctionComparison q).hom.app F) ≫
        (pullbackCompOfEq p q t h F).hom =
      (overlapAdjunctionComparison t).hom.app F := by
  subst t
  let ap := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction p)
  let aq := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction q)
  let aT := Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction (p ≫ q))
  let bp := Scheme.Modules.pullbackPushforwardAdjunction p
  let bq := Scheme.Modules.pullbackPushforwardAdjunction q
  let bt := Scheme.Modules.pullbackPushforwardAdjunction (p ≫ q)
  have hs : conjugateEquiv (aq.comp ap) aT
      (Scheme.Modules.tensorPullbackCompositionIso p q (p ≫ q) rfl).hom =
      (Scheme.Modules.pushforwardComp p q).hom := by
    have hr : Scheme.Modules.pushforwardCongr (rfl : p ≫ q = p ≫ q) =
        Iso.refl _ := by
      apply Iso.ext
      apply NatTrans.ext
      funext N
      apply Scheme.Modules.hom_ext
      intro U
      simp
    simp [Scheme.Modules.tensorPullbackCompositionIso, hr, conjugateIsoEquiv, aq, ap, aT]
  have hn :
      (Scheme.Modules.tensorPullbackCompositionIso p q (p ≫ q) rfl).hom ≫
        Functor.whiskerLeft (Scheme.Modules.tensorPullback q)
          (overlapAdjunctionComparison p).hom ≫
        Functor.whiskerRight (overlapAdjunctionComparison q).hom
          (Scheme.Modules.pullback p) =
      (overlapAdjunctionComparison (p ≫ q)).hom ≫
        (Scheme.Modules.pullbackComp p q).inv := by
    apply (conjugateEquiv (bq.comp bp) aT).injective
    rw [← Category.assoc, ← conjugateEquiv_comp (bq.comp bp) (aq.comp bp) aT,
      ← conjugateEquiv_comp (aq.comp bp) (aq.comp ap) aT,
      ← conjugateEquiv_comp (bq.comp bp) bt aT,
      conjugateEquiv_whiskerRight bq aq bp,
      conjugateEquiv_whiskerLeft bp ap aq]
    simp only [bq, bp, bt, aq, ap, aT, eta_mate,
      Category.comp_id, Scheme.Modules.conjugateEquiv_pullbackComp_inv] at *
    exact hs
  have hnF := congrArg (fun n ↦ n.app F) hn
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app] at hnF
  rw [pc_refl]
  rw [← cancel_mono ((Scheme.Modules.pullbackComp p q).inv.app F)]
  simp only [Iso.app_hom, Category.assoc, Iso.hom_inv_id_app]
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id ((Scheme.Modules.pullback p).map
    ((overlapAdjunctionComparison q).hom.app F))]
  exact hnF

private theorem pc_assoc_iso
    {W X Y Z : Scheme.{u}} (f : W ⟶ Z) (g : Z ⟶ Y) (h : Y ⟶ X)
    (a : W ⟶ Y) (b : Z ⟶ X) (c : W ⟶ X)
    (ha : f ≫ g = a) (hb : g ≫ h = b) (hc : a ≫ h = c)
    (hc' : f ≫ b = c) (M : X.Modules) :
    (Scheme.Modules.pullback f).mapIso (pullbackCompOfEq g h b hb M) ≪≫
        pullbackCompOfEq f b c hc' M =
      pullbackCompOfEq f g a ha ((Scheme.Modules.pullback h).obj M) ≪≫
        pullbackCompOfEq a h c hc M := by
  apply Iso.ext
  exact pc_assoc f g h a b c ha hb hc hc' M

private theorem pc_nat_iso {X Y Z : Scheme.{u}}
    (f : Z ⟶ Y) (g : Y ⟶ X) (a : Z ⟶ X) (ha : f ≫ g = a)
    {M N : X.Modules} (e : M ≅ N) :
    (Scheme.Modules.pullback f).mapIso ((Scheme.Modules.pullback g).mapIso e) ≪≫
        pullbackCompOfEq f g a ha N =
      pullbackCompOfEq f g a ha M ≪≫ (Scheme.Modules.pullback a).mapIso e := by
  apply Iso.ext
  unfold pullbackCompOfEq
  simp only [Functor.mapIso_hom, Iso.trans_hom, Iso.app_hom]
  exact ((Scheme.Modules.pullbackComp f g ≪≫
    Scheme.Modules.pullbackCongr ha).hom.naturality e.hom)

private theorem tensor_compat_iso {X Y Z : Scheme.{u}}
    (p : Z ⟶ Y) (q : Y ⟶ X) (t : Z ⟶ X) (h : p ≫ q = t) (F : X.Modules) :
    (Scheme.Modules.tensorPullbackCompositionIso p q t h).app F ≪≫
        (overlapAdjunctionComparison p).app ((Scheme.Modules.tensorPullback q).obj F) ≪≫
        (Scheme.Modules.pullback p).mapIso ((overlapAdjunctionComparison q).app F) ≪≫
        pullbackCompOfEq p q t h F =
      (overlapAdjunctionComparison t).app F := by
  apply Iso.ext
  exact tensor_compat p q t h F

/-- Factorization of one canonical chart comparison through the stage model.
Source: Stacks Project, Tags 0095, 0096 and 0097 (composition of inverse images and
uniqueness of their adjunction comparisons); Tag 01ZR (2), first proof.
(blueprint: lem-pc-overlap-model-chart-factorization).

Proof: Expand the direct and stage model comparisons. The tensor composition
comparison followed by the comparisons from tensor to abstract pullback equals
abstract pullback composition followed by the comparison for the composite.
Indeed, apply the conjugation equivalence for the composite adjunctions: both
maps correspond to pushforward composition followed by congruence along h₀.
Whisker this equality by pullback along z. Use naturality to move the comparison
for q₀ through the composition isomorphisms, and use the pullback composition
pentagon on the triples (z, p₀, q₀), (l, d, q₀), and the subsequent map r₀.
The equation hz identifies their composite routes. The equations hk, hl, htr,
hvu, hδ and hzv identify both exterior routes to A. The remaining composition
comparisons cancel in inverse pairs, giving the displayed factorization.
Only invertible canonical comparisons are used. The argument also works for
identity maps, zero module sheaves and empty schemes; no faithfulness is needed. -/
theorem overlap_model_chart_factorization
    {H₀ Hₖ H K L A B C D : Scheme.{u}}
    (q₀ : Hₖ ⟶ H₀) (p₀ : H ⟶ Hₖ) (t₀ : H ⟶ H₀) (h₀ : p₀ ≫ q₀ = t₀)
    (r₀ : H₀ ⟶ A) (d : K ⟶ Hₖ) (s : K ⟶ B) (u : B ⟶ A)
    (hk : (d ≫ q₀) ≫ r₀ = s ≫ u)
    (v : H ⟶ C) (u' : C ⟶ A) (k : H ⟶ A)
    (htr : t₀ ≫ r₀ = k) (hvu : v ≫ u' = k)
    (z : L ⟶ H) (l : L ⟶ K) (hz : z ≫ p₀ = l ≫ d)
    (r : L ⟶ D) (w : D ⟶ B) (δ : D ⟶ C)
    (hl : l ≫ s = r ≫ w) (hδ : δ ≫ u' = w ≫ u) (hzv : z ≫ v = r ≫ δ)
    (N : A.Modules) :
    let F := (Scheme.Modules.pullback r₀).obj N
    let σ := Scheme.Modules.tensorPullbackCompositionIso p₀ q₀ t₀ h₀
    let E := Functor.isoWhiskerRight (overlapAdjunctionComparison p₀)
        (Scheme.Modules.pullback z) ≪≫
      Scheme.Modules.pullbackComp z p₀ ≪≫ Scheme.Modules.pullbackCongr hz ≪≫
      (Scheme.Modules.pullbackComp l d).symm
    let τ := overlapDirectModelComparison t₀ r₀ k v u' htr hvu N
    let ξ := (Scheme.Modules.pullback z).mapIso τ ≪≫
      pullbackCompOfEq z v (r ≫ δ) hzv ((Scheme.Modules.pullback u').obj N) ≪≫
      ((Scheme.Modules.pullbackComp r δ).app _).symm ≪≫
      (Scheme.Modules.pullback r).mapIso
        ((Scheme.Modules.pullbackComp w u).app N ≪≫
          (Scheme.Modules.pullbackCongr hδ.symm).app N ≪≫
          ((Scheme.Modules.pullbackComp δ u').app N).symm).symm
    let s' := overlapStageModelComparison d q₀ r₀ s u hk N
    let β := pullbackCompOfEq l s (r ≫ w) hl ((Scheme.Modules.pullback u).obj N) ≪≫
      ((Scheme.Modules.pullbackComp r w).app _).symm
    ξ = (Scheme.Modules.pullback z).mapIso (σ.app F) ≪≫
      E.app ((Scheme.Modules.tensorPullback q₀).obj F) ≪≫
      (Scheme.Modules.pullback l).mapIso s' ≪≫ β := by
  dsimp only
  let n := (r ≫ w) ≫ u
  have hrd : (r ≫ δ) ≫ u' = n := by
    dsimp only [n]
    simp only [Category.assoc, hδ]
  have hzk : z ≫ k = n := by
    rw [← hvu, ← Category.assoc, hzv]
    exact hrd
  let J := (Scheme.Modules.pullbackComp r w).app
      ((Scheme.Modules.pullback u).obj N) ≪≫
    pullbackCompOfEq (r ≫ w) u n rfl N
  have hinner :
      ((Scheme.Modules.pullbackComp r δ).app ((Scheme.Modules.pullback u').obj N)).symm ≪≫
        (Scheme.Modules.pullback r).mapIso
          ((Scheme.Modules.pullbackComp w u).app N ≪≫
            (Scheme.Modules.pullbackCongr hδ.symm).app N ≪≫
            ((Scheme.Modules.pullbackComp δ u').app N).symm).symm ≪≫ J =
      pullbackCompOfEq (r ≫ δ) u' n hrd N := by
    dsimp only [J]
    rw [← pc_refl r w, ← pc_assoc_iso r w u (r ≫ w) (w ≫ u) n
      rfl rfl rfl (by simp only [n, Category.assoc]) N, pc_refl w u]
    simp only [Iso.trans_symm, Functor.mapIso_trans, Functor.mapIso_symm,
      Iso.trans_assoc, Iso.symm_self_id_assoc, Iso.symm_symm_eq]
    have hcongr : (Scheme.Modules.pullbackCongr hδ.symm).symm =
        Scheme.Modules.pullbackCongr hδ := by
      unfold Scheme.Modules.pullbackCongr
      rfl
    rw [← Functor.mapIso_symm]
    change ((Scheme.Modules.pullbackComp r δ).app _).symm ≪≫
      (Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullbackComp δ u').app N) ≪≫
      (Scheme.Modules.pullback r).mapIso
        ((Scheme.Modules.pullbackCongr hδ.symm).symm.app N) ≪≫ _ = _
    rw [hcongr, ← Iso.trans_assoc
      ((Scheme.Modules.pullback r).mapIso ((Scheme.Modules.pullbackComp δ u').app N)),
      ← Functor.mapIso_trans]
    rw [← pc_def δ u' (w ≫ u) hδ N]
    rw [pc_assoc_iso r δ u' (r ≫ δ) (w ≫ u) n rfl hδ hrd
      (by simp only [n, Category.assoc]) N, pc_refl r δ]
    exact Iso.symm_self_id_assoc _ _
  have htail :
      pullbackCompOfEq z v (r ≫ δ) hzv ((Scheme.Modules.pullback u').obj N) ≪≫
        ((Scheme.Modules.pullbackComp r δ).app _).symm ≪≫
        (Scheme.Modules.pullback r).mapIso
          ((Scheme.Modules.pullbackComp w u).app N ≪≫
            (Scheme.Modules.pullbackCongr hδ.symm).app N ≪≫
            ((Scheme.Modules.pullbackComp δ u').app N).symm).symm ≪≫ J =
      (Scheme.Modules.pullback z).mapIso (pullbackCompOfEq v u' k hvu N) ≪≫
        pullbackCompOfEq z k n hzk N := by
    rw [hinner, pc_assoc_iso z v u' (r ≫ δ) k n hzv hvu hrd hzk N]
  have hlsu : l ≫ (s ≫ u) = n := by
    rw [← Category.assoc, hl]
  have hldr : (l ≫ (d ≫ q₀)) ≫ r₀ = n := by
    rw [Category.assoc, hk]
    exact hlsu
  have hldq : (l ≫ d) ≫ q₀ = l ≫ (d ≫ q₀) := Category.assoc _ _ _
  have hstage :
      ((Scheme.Modules.pullbackComp l d).app
        ((Scheme.Modules.tensorPullback q₀).obj ((Scheme.Modules.pullback r₀).obj N))).symm ≪≫
        (Scheme.Modules.pullback l).mapIso
          (overlapStageModelComparison d q₀ r₀ s u hk N) ≪≫
        (pullbackCompOfEq l s (r ≫ w) hl ((Scheme.Modules.pullback u).obj N) ≪≫
          ((Scheme.Modules.pullbackComp r w).app _).symm) ≪≫ J =
      (Scheme.Modules.pullback (l ≫ d)).mapIso
          ((overlapAdjunctionComparison q₀).app ((Scheme.Modules.pullback r₀).obj N)) ≪≫
        pullbackCompOfEq (l ≫ d) q₀ (l ≫ (d ≫ q₀)) hldq
          ((Scheme.Modules.pullback r₀).obj N) ≪≫
        pullbackCompOfEq (l ≫ (d ≫ q₀)) r₀ n hldr N := by
    simp only [J, overlapStageModelComparison, Functor.mapIso_trans, Iso.trans_assoc,
      Iso.symm_self_id_assoc]
    rw [← pc_assoc_iso l s u (r ≫ w) (s ≫ u) n hl rfl rfl hlsu N,
      pc_refl s u]
    simp only [Functor.mapIso_symm, Iso.symm_self_id_assoc]
    rw [← pc_refl d q₀, pc_assoc_iso l (d ≫ q₀) r₀ (l ≫ (d ≫ q₀)) (s ≫ u)
      n rfl hk hldr hlsu N]
    rw [← Iso.trans_assoc ((Scheme.Modules.pullback l).mapIso
      (pullbackCompOfEq d q₀ (d ≫ q₀) rfl ((Scheme.Modules.pullback r₀).obj N))),
      pc_assoc_iso l d q₀ (l ≫ d) (d ≫ q₀) (l ≫ (d ≫ q₀))
        rfl rfl hldq rfl ((Scheme.Modules.pullback r₀).obj N)]
    simp only [Iso.trans_assoc]
    rw [← Iso.trans_assoc ((Scheme.Modules.pullback l).mapIso
      ((Scheme.Modules.pullback d).mapIso
        ((overlapAdjunctionComparison q₀).app ((Scheme.Modules.pullback r₀).obj N)))),
      pc_nat_iso l d (l ≫ d) rfl
      ((overlapAdjunctionComparison q₀).app ((Scheme.Modules.pullback r₀).obj N)),
      pc_refl l d]
    simp only [Iso.trans_assoc, Iso.symm_self_id_assoc]
  have hzt : z ≫ t₀ = l ≫ (d ≫ q₀) := by
    rw [← h₀, ← Category.assoc, hz, Category.assoc]
  have he :
      (Functor.isoWhiskerRight (overlapAdjunctionComparison p₀)
        (Scheme.Modules.pullback z)).app
          ((Scheme.Modules.tensorPullback q₀).obj ((Scheme.Modules.pullback r₀).obj N)) =
      (Scheme.Modules.pullback z).mapIso
        ((overlapAdjunctionComparison p₀).app
          ((Scheme.Modules.tensorPullback q₀).obj ((Scheme.Modules.pullback r₀).obj N))) := rfl
  apply Iso.ext
  rw [← cancel_mono J.hom]
  change (_ ≪≫ J).hom = (_ ≪≫ J).hom
  apply congrArg Iso.hom
  simp only [NatIso.trans_app, Iso.trans_assoc]
  rw [htail, he]
  simp only [Iso.trans_assoc] at hstage
  rw [pc_symm_app, hstage]
  simp only [overlapDirectModelComparison, Functor.mapIso_trans, Functor.mapIso_symm,
    Iso.trans_assoc, Iso.symm_self_id_assoc]
  rw [← Iso.trans_assoc
    ((Scheme.Modules.pullbackComp z p₀).app
      ((Scheme.Modules.tensorPullback q₀).obj ((Scheme.Modules.pullback r₀).obj N))),
    ← pc_def z p₀ (l ≫ d) hz]
  rw [← Iso.trans_assoc
    (pullbackCompOfEq z p₀ (l ≫ d) hz
      ((Scheme.Modules.tensorPullback q₀).obj ((Scheme.Modules.pullback r₀).obj N))),
    ← pc_nat_iso z p₀ (l ≫ d) hz
      ((overlapAdjunctionComparison q₀).app ((Scheme.Modules.pullback r₀).obj N))]
  simp only [Iso.trans_assoc]
  rw [← Iso.trans_assoc
    (pullbackCompOfEq z p₀ (l ≫ d) hz
      ((Scheme.Modules.pullback q₀).obj ((Scheme.Modules.pullback r₀).obj N))),
    ← pc_assoc_iso z p₀ q₀ (l ≫ d) t₀ (l ≫ (d ≫ q₀)) hz h₀ hldq hzt
      ((Scheme.Modules.pullback r₀).obj N)]
  simp only [Iso.trans_assoc]
  rw [pc_assoc_iso z t₀ r₀ (l ≫ (d ≫ q₀)) k n hzt htr hldr hzk N]
  have htc := congrArg ((Scheme.Modules.pullback z).mapIso)
    (tensor_compat_iso p₀ q₀ t₀ h₀ ((Scheme.Modules.pullback r₀).obj N))
  simp only [Functor.mapIso_trans] at htc
  have htc' := congrArg (fun i ↦ i ≪≫
    pullbackCompOfEq z t₀ (l ≫ (d ≫ q₀)) hzt ((Scheme.Modules.pullback r₀).obj N) ≪≫
      pullbackCompOfEq (l ≫ (d ≫ q₀)) r₀ n hldr N) htc
  simpa only [Iso.trans_assoc] using htc'.symm


end
end AlgebraicGeometry
