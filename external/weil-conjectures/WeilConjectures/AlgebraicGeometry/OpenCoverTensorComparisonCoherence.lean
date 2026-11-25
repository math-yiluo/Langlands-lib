/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OpenCoverRefinementComparisons
import WeilConjectures.AlgebraicGeometry.OpenCoverTensorRecoveryNormalization
import WeilConjectures.AlgebraicGeometry.OrdinaryPullbackRefinementCoherence

/-! # Coherence of tensor pullback comparisons on refined charts

Source: Stacks Project, Tags 0095 and 0096, functoriality of module pullback.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules

private theorem assemble_refinement_comparisons
    {C E F D K L : Type*}
    [Category* C] [Category* E] [Category* F] [Category* D] [Category* K] [Category* L]
    (T T' : C ⥤ E) (Ak Bk : C ⥤ D) (Al Bl : C ⥤ F)
    (Dfun : D ⥤ F) (Pk : D ⥤ K) (Pl : F ⥤ L)
    (Zf : K ⥤ L) (Rk : E ⥤ K) (Rl : E ⥤ L)
    (c : T ≅ T') (tk : Bk ≅ Ak) (tl : Bl ≅ Al)
    (gamma : Bl ≅ Bk ⋙ Dfun) (alpha : Al ≅ Ak ⋙ Dfun)
    (beta : Rk ⋙ Zf ≅ Rl) (delta : Pk ⋙ Zf ≅ Dfun ⋙ Pl)
    (ck : T ⋙ Rk ≅ Ak ⋙ Pk) (cl : T ⋙ Rl ≅ Al ⋙ Pl)
    (rhoK : T' ⋙ Rk ≅ Bk ⋙ Pk) (rhoL : T' ⋙ Rl ≅ Bl ⋙ Pl)
    (hAlpha : alpha = tl.symm ≪≫ gamma ≪≫ Functor.isoWhiskerRight tk Dfun)
    (M : C)
    (hk : ck.hom.app M ≫ Pk.map (tk.inv.app M) =
      Rk.map (c.hom.app M) ≫ rhoK.hom.app M)
    (hl : cl.hom.app M ≫ Pl.map (tl.inv.app M) =
      Rl.map (c.hom.app M) ≫ rhoL.hom.app M)
    (ho : Zf.map (rhoK.hom.app M) ≫ delta.hom.app (Bk.obj M) ≫
      Pl.map (gamma.inv.app M) = beta.hom.app (T'.obj M) ≫ rhoL.hom.app M) :
    Zf.map (ck.hom.app M) ≫ delta.hom.app (Ak.obj M) ≫ Pl.map (alpha.inv.app M) =
      beta.hom.app (T.obj M) ≫ cl.hom.app M := by
  have ha : alpha.inv.app M ≫ tl.inv.app M =
      Dfun.map (tk.inv.app M) ≫ gamma.inv.app M := by
    rw [hAlpha]
    simp only [Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app,
      Functor.isoWhiskerRight_inv, Functor.whiskerRight_app,
      Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  apply (cancel_mono (Pl.map (tl.inv.app M))).1
  calc
    (Zf.map (ck.hom.app M) ≫ delta.hom.app (Ak.obj M) ≫
        Pl.map (alpha.inv.app M)) ≫ Pl.map (tl.inv.app M) =
        Zf.map (ck.hom.app M) ≫ delta.hom.app (Ak.obj M) ≫
          Pl.map (Dfun.map (tk.inv.app M)) ≫ Pl.map (gamma.inv.app M) := by
      simp only [Category.assoc, ← Pl.map_comp, ha]
    _ = Zf.map (ck.hom.app M ≫ Pk.map (tk.inv.app M)) ≫
        delta.hom.app (Bk.obj M) ≫ Pl.map (gamma.inv.app M) := by
      have hn := delta.hom.naturality (tk.inv.app M)
      change Zf.map (Pk.map (tk.inv.app M)) ≫ delta.hom.app (Bk.obj M) =
        delta.hom.app (Ak.obj M) ≫ Pl.map (Dfun.map (tk.inv.app M)) at hn
      rw [Zf.map_comp]
      simp only [Category.assoc]
      rw [← Category.assoc (delta.hom.app _) (Pl.map _) _, ← hn]
      simp only [Category.assoc]
    _ = Zf.map (Rk.map (c.hom.app M)) ≫
        (beta.hom.app (T'.obj M) ≫ rhoL.hom.app M) := by
      rw [hk, Zf.map_comp]
      simpa only [Category.assoc] using congrArg
        (fun t ↦ Zf.map (Rk.map (c.hom.app M)) ≫ t) ho
    _ = (beta.hom.app (T.obj M) ≫ cl.hom.app M) ≫
        Pl.map (tl.inv.app M) := by
      have hn := beta.hom.naturality (c.hom.app M)
      change Zf.map (Rk.map (c.hom.app M)) ≫ beta.hom.app (T'.obj M) =
        beta.hom.app (T.obj M) ≫ Rl.map (c.hom.app M) at hn
      rw [← Category.assoc, hn, Category.assoc, ← hl, ← Category.assoc]


attribute [local irreducible] tensorPullback tensorPullbackCompositionIso
  openCoverTensorPullbackComparison moduleRecoveryComparisonIso pullbackComp pullbackCongr

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The restriction/composition comparison is compatible with a chart refinement.
Source: Stacks Project, Tags 0095 and 0096; the canonical-comparison step in
lem-pc-open-cover-map-lift-transport.
(blueprint: lem-pc-open-cover-tensor-comparison-coherence).

Proof: For every scheme map b, let c_b be the unique comparison from its
fixed tensor left adjoint to its ordinary pullback left adjoint. Transposing
under the fixed adjunctions shows that tensorPullbackCompositionIso(g,b,t,w)
is the composite of c_t, congruence from t to g ≫ b, inverse ordinary pullback
composition, and the inverses of c_b and c_g on the two functor factors:
both transposes are pushforwardComp(g,b) followed by pushforwardCongr(w).
Injectivity of the adjunction conjugation gives this formula. The chart
comparison is, by its definition, ordinary composition/congruence followed by
the inverse of c_b on the base-map factor.
Substitute these formulas in alpha, ck and cl from the comparison bundle.
Functoriality moves each c_b through whiskering, and the adjacent c_b and
c_b inverse factors cancel. The remaining assertion involves only ordinary
pullback composition and pullback congruence. Its two paths are the reassociated
pullbacks of the same map from Vl(a) to U(a): hz identifies the route through
d and the chart map of Vk, hd identifies the route from Ul to U(a), and hz0
identifies the maps to W. Apply Scheme.Modules.pseudofunctor_associativity to
these reassociations; congruence along the stated scheme equalities identifies
the composites, independently of their equality proof witnesses. Restore the
cancelled comparisons and evaluate at M. This proves precisely the displayed
identity, including identity refinements, empty charts and zero modules. -/
theorem openCover_tensor_comparison_coherence
    {X Y Z W : Scheme.{u}} (q : Y ⟶ X) (v : Z ⟶ X) (h : W ⟶ X)
    (pk : W ⟶ Y) (pl : W ⟶ Z) (wk : pk ≫ q = h) (wl : pl ≫ v = h)
    (U : X.OpenCover.{u}) (a : U.I₀)
    (d : (U.pullback₁ v).X a ⟶ (U.pullback₁ q).X a)
    (hd : d ≫ U.pullbackHom q a = U.pullbackHom v a)
    (z : ((U.pullback₁ v).pullback₁ pl).X a ⟶
      ((U.pullback₁ q).pullback₁ pk).X a)
    (hz : z ≫ Scheme.Cover.pullbackHom (U.pullback₁ q) pk a =
      Scheme.Cover.pullbackHom (U.pullback₁ v) pl a ≫ d)
    (hz0 : z ≫ ((U.pullback₁ q).pullback₁ pk).f a =
      ((U.pullback₁ v).pullback₁ pl).f a)
    (M : X.Modules) :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let Ul : Z.OpenCover.{u} := U.pullback₁ v
    let Vk : W.OpenCover.{u} := Uk.pullback₁ pk
    let Vl : W.OpenCover.{u} := Ul.pullback₁ pl
    let D := pullback d
    let Pk := pullback (Uk.pullbackHom pk a)
    let Pl := pullback (Ul.pullbackHom pl a)
    let Zf := pullback z
    let Rk := pullback (Vk.f a)
    let Rl := pullback (Vl.f a)
    let Lk := tensorPullback q ⋙ pullback (Uk.f a)
    let Ll := tensorPullback v ⋙ pullback (Ul.f a)
    let comparisons := openCoverRefinementComparisons q v h pk pl wk wl U a d hd z hz hz0
    let alpha := comparisons.1
    let beta := comparisons.2.1
    let delta := comparisons.2.2.1
    let ck := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback q)
      (tensorPullback pk) (pullback (Uk.f a)) Pk Rk
      (tensorPullbackCompositionIso pk q h wk) (openCoverTensorPullbackComparison pk Uk a)
    let cl := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback v)
      (tensorPullback pl) (pullback (Ul.f a)) Pl Rl
      (tensorPullbackCompositionIso pl v h wl) (openCoverTensorPullbackComparison pl Ul a)
    Zf.map (ck.hom.app M) ≫ delta.hom.app (Lk.obj M) ≫
      Pl.map (alpha.inv.app M) = beta.hom.app ((tensorPullback h).obj M) ≫
        cl.hom.app M := by
  intro Uk Ul Vk Vl D Pk Pl Zf Rk Rl Lk Ll comparisons alpha beta delta ck cl
  let S := pullback (U.f a)
  let Qk := pullback (U.pullbackHom q a)
  let Ql := pullback (U.pullbackHom v a)
  let tk := openCoverTensorPullbackComparison q U a
  let tl := openCoverTensorPullbackComparison v U a
  let gamma : S ⋙ Ql ≅ (S ⋙ Qk) ⋙ D :=
    Functor.isoWhiskerLeft S
      ((pullbackCongr hd).symm ≪≫ (pullbackComp d (U.pullbackHom q a)).symm) ≪≫
      (Functor.associator S Qk D).symm
  have Hk : (Uk.pullbackHom pk a ≫ U.pullbackHom q a) ≫ U.f a = Vk.f a ≫ h := by
    rw [Category.assoc, U.pullbackHom_map q a, ← Category.assoc,
      Uk.pullbackHom_map pk a, Category.assoc, wk]
  have Hl : (Ul.pullbackHom pl a ≫ U.pullbackHom v a) ≫ U.f a = Vl.f a ≫ h := by
    rw [Category.assoc, U.pullbackHom_map v a, ← Category.assoc,
      Ul.pullbackHom_map pl a, Category.assoc, wl]
  let c := Adjunction.leftAdjointUniq
    (Classical.choose (exists_tensorPullbackAdjunction h)) (pullbackPushforwardAdjunction h)
  let rhoK : pullback h ⋙ Rk ≅ (S ⋙ Qk) ⋙ Pk :=
    pullbackComp (Vk.f a) h ≪≫ (pullbackCongr Hk).symm ≪≫
      (pullbackComp (Uk.pullbackHom pk a ≫ U.pullbackHom q a) (U.f a)).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp (Uk.pullbackHom pk a)
        (U.pullbackHom q a)).symm ≪≫ (Functor.associator S Qk Pk).symm
  let rhoL : pullback h ⋙ Rl ≅ (S ⋙ Ql) ⋙ Pl :=
    pullbackComp (Vl.f a) h ≪≫ (pullbackCongr Hl).symm ≪≫
      (pullbackComp (Ul.pullbackHom pl a ≫ U.pullbackHom v a) (U.f a)).symm ≪≫
      Functor.isoWhiskerLeft S (pullbackComp (Ul.pullbackHom pl a)
        (U.pullbackHom v a)).symm ≪≫ (Functor.associator S Ql Pl).symm
  have hk : ck.hom.app M ≫ Pk.map (tk.inv.app M) =
      Rk.map (c.hom.app M) ≫ rhoK.hom.app M :=
    openCover_tensor_recovery_normalization q pk h wk U a Hk c rfl tk rfl ck rfl rhoK rfl M
  have hl : cl.hom.app M ≫ Pl.map (tl.inv.app M) =
      Rl.map (c.hom.app M) ≫ rhoL.hom.app M :=
    openCover_tensor_recovery_normalization v pl h wl U a Hl c rfl tl rfl cl rfl rhoL rfl M
  have ho : Zf.map (rhoK.hom.app M) ≫ delta.hom.app ((S ⋙ Qk).obj M) ≫
      Pl.map (gamma.inv.app M) = beta.hom.app ((pullback h).obj M) ≫ rhoL.hom.app M :=
    ordinary_pullback_refinement_coherence (U.f a) (U.pullbackHom q a)
      (U.pullbackHom v a) (Uk.pullbackHom pk a) (Ul.pullbackHom pl a)
      (Vk.f a) (Vl.f a) h d z hd hz hz0 Hk Hl M rhoK rfl rhoL rfl gamma rfl beta rfl delta rfl
  exact assemble_refinement_comparisons (tensorPullback h) (pullback h)
    Lk (S ⋙ Qk) Ll (S ⋙ Ql) D Pk Pl Zf Rk Rl c tk tl gamma alpha beta delta
    ck cl rhoK rhoL rfl M hk hl ho

end AlgebraicGeometry.Scheme.Modules
