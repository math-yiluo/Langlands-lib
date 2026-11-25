/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.OpenCoverTensorComparisonCoherence

/-! # Transport of a supplied chart map lift to later stages

Source: Stacks Project, Sheaves of Modules, Tags 0095 and 0096,
and Limits Tag 01ZR, persistence under further base change.
(blueprint: lem-pc-open-cover-map-lift-transport).
-/

set_option cleanup.letToHave false

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

namespace Scheme.Modules

private theorem recovery_iff
    {C : Type*} [Category* C] {A B C' D E F : C}
    (e : A ≅ B) (e' : D ≅ E) (t : B ≅ C') (t' : E ≅ F)
    (φ : A ⟶ D) (r : C' ⟶ F) :
    t.hom ≫ r ≫ t'.inv = e.inv ≫ φ ≫ e'.hom ↔
      (e.hom ≫ t.hom) ≫ r = φ ≫ e'.hom ≫ t'.hom := by
  constructor
  · intro hr
    have hh := congrArg (fun f ↦ e.hom ≫ f ≫ t'.hom) hr
    simpa only [Category.assoc, Iso.inv_hom_id, Iso.inv_hom_id_assoc,
      Iso.hom_inv_id_assoc, Category.id_comp, Category.comp_id] using hh
  · intro hr
    have hh := congrArg (fun f ↦ e.inv ≫ f ≫ t'.inv) hr
    simpa only [Category.assoc, Iso.inv_hom_id_assoc, Iso.hom_inv_id,
      Category.id_comp, Category.comp_id] using hh

private theorem transport_square
    {C H K L V W : Type*}
    [Category* C] [Category* H] [Category* K] [Category* L] [Category* V] [Category* W]
    (A : C ⥤ H) (Lk : C ⥤ K) (Ll : C ⥤ L)
    (Pk : K ⥤ V) (Pl : L ⥤ W) (D : K ⥤ L) (Zf : V ⥤ W)
    (Rk : H ⥤ V) (Rl : H ⥤ W)
    (alpha : Ll ≅ Lk ⋙ D) (beta : Rk ⋙ Zf ≅ Rl) (delta : Pk ⋙ Zf ≅ D ⋙ Pl)
    (ck : A ⋙ Rk ≅ Lk ⋙ Pk) (cl : A ⋙ Rl ≅ Ll ⋙ Pl)
    (coherence : ∀ M, Zf.map (ck.hom.app M) ≫ delta.hom.app (Lk.obj M) ≫
      Pl.map (alpha.inv.app M) = beta.hom.app (A.obj M) ≫ cl.hom.app M)
    {F G : C} (φ : A.obj F ⟶ A.obj G) (r : Lk.obj F ⟶ Lk.obj G)
    (hr : ck.hom.app F ≫ Pk.map r = Rk.map φ ≫ ck.hom.app G) :
    cl.hom.app F ≫ Pl.map (alpha.hom.app F ≫ D.map r ≫ alpha.inv.app G) =
      Rl.map φ ≫ cl.hom.app G := by
  apply (cancel_epi (beta.hom.app (A.obj F))).mp
  rw [← Category.assoc, ← coherence F]
  simp only [Functor.map_comp, Category.assoc]
  rw [← Pl.map_comp_assoc, alpha.inv_hom_id_app]
  erw [Pl.map_id, Category.id_comp]
  erw [← delta.hom.naturality_assoc r]
  change Zf.map (ck.hom.app F) ≫ Zf.map (Pk.map r) ≫
    delta.hom.app (Lk.obj G) ≫ Pl.map (alpha.inv.app G) = _
  rw [← Zf.map_comp_assoc, hr, Zf.map_comp, Category.assoc, coherence G]
  erw [← Category.assoc, beta.hom.naturality φ]
  simp only [Category.assoc]

private theorem recovery_square_iff
    {C E D K V : Type*}
    [Category* C] [Category* E] [Category* D] [Category* K] [Category* V]
    (T : C ⥤ D) (A : C ⥤ E) (B : E ⥤ D) (S : E ⥤ K) (P : K ⥤ V) (R : D ⥤ V)
    (e : T ≅ A ⋙ B) (t : S ⋙ P ≅ B ⋙ R)
    {F G : C} (φ : T.obj F ⟶ T.obj G) (r : S.obj (A.obj F) ⟶ S.obj (A.obj G)) :
    let ck := moduleRecoveryComparisonIso T A B S P R e t
    (t.inv.app _ ≫ P.map r ≫ t.hom.app _ = R.map (e.inv.app F ≫ φ ≫ e.hom.app G)) ↔
      ck.hom.app F ≫ P.map r = R.map φ ≫ ck.hom.app G := by
  intro ck
  simpa only [ck, moduleRecoveryComparisonIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Category.id_comp, Category.comp_id, Category.assoc, Functor.map_comp,
    Functor.mapIso_hom, Functor.mapIso_inv, Iso.app_hom, Iso.app_inv, Iso.symm_inv]
    using recovery_iff (R.mapIso (e.app F)) (R.mapIso (e.app G))
      (t.symm.app (A.obj F)) (t.symm.app (A.obj G)) (R.map φ) (P.map r)

private theorem transport_recovery
    {C H K L V W Ek El : Type*}
    [Category* C] [Category* H] [Category* K] [Category* L] [Category* V] [Category* W]
    [Category* Ek] [Category* El]
    (T : C ⥤ H) (Ak : C ⥤ Ek) (Al : C ⥤ El) (Bk : Ek ⥤ H) (Bl : El ⥤ H)
    (Sk : Ek ⥤ K) (Sl : El ⥤ L) (Pk : K ⥤ V) (Pl : L ⥤ W)
    (Rk : H ⥤ V) (Rl : H ⥤ W) (D : K ⥤ L) (Zf : V ⥤ W)
    (ek : T ≅ Ak ⋙ Bk) (el : T ≅ Al ⋙ Bl)
    (tk : Sk ⋙ Pk ≅ Bk ⋙ Rk) (tl : Sl ⋙ Pl ≅ Bl ⋙ Rl)
    (alpha : Al ⋙ Sl ≅ (Ak ⋙ Sk) ⋙ D)
    (beta : Rk ⋙ Zf ≅ Rl) (delta : Pk ⋙ Zf ≅ D ⋙ Pl)
    (coherence : ∀ M,
      Zf.map ((moduleRecoveryComparisonIso T Ak Bk Sk Pk Rk ek tk).hom.app M) ≫
        delta.hom.app ((Ak ⋙ Sk).obj M) ≫ Pl.map (alpha.inv.app M) =
      beta.hom.app (T.obj M) ≫
        (moduleRecoveryComparisonIso T Al Bl Sl Pl Rl el tl).hom.app M)
    {F G : C} (φ : T.obj F ⟶ T.obj G) (r : Sk.obj (Ak.obj F) ⟶ Sk.obj (Ak.obj G))
    (hr : tk.inv.app _ ≫ Pk.map r ≫ tk.hom.app _ =
      Rk.map (ek.inv.app F ≫ φ ≫ ek.hom.app G)) :
    tl.inv.app _ ≫ Pl.map (alpha.hom.app F ≫ D.map r ≫ alpha.inv.app G) ≫ tl.hom.app _ =
      Rl.map (el.inv.app F ≫ φ ≫ el.hom.app G) := by
  have hr' := (recovery_square_iff T Ak Bk Sk Pk Rk ek tk φ r).mp hr
  have recovered := transport_square T (Ak ⋙ Sk) (Al ⋙ Sl) Pk Pl D Zf Rk Rl
    alpha beta delta (moduleRecoveryComparisonIso T Ak Bk Sk Pk Rk ek tk)
    (moduleRecoveryComparisonIso T Al Bl Sl Pl Rl el tl) coherence φ r hr'
  exact (recovery_square_iff T Al Bl Sl Pl Rl el tl φ
    (alpha.hom.app F ≫ D.map r ≫ alpha.inv.app G)).mpr recovered

attribute [local irreducible] tensorPullbackCompositionIso openCoverTensorPullbackComparison
  pullback pullbackComp pullbackCongr tensorPullback

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem transport_chart_map
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
    (F G : X.Modules)
    (φ : (tensorPullback h).obj F ⟶ (tensorPullback h).obj G) :
    let Uk : Y.OpenCover.{u} := U.pullback₁ q
    let Ul : Z.OpenCover.{u} := U.pullback₁ v
    let Vk : W.OpenCover.{u} := Uk.pullback₁ pk
    let Vl : W.OpenCover.{u} := Ul.pullback₁ pl
    let ek := tensorPullbackCompositionIso pk q h wk
    let el := tensorPullbackCompositionIso pl v h wl
    let tk := openCoverTensorPullbackComparison pk Uk a
    let tl := openCoverTensorPullbackComparison pl Ul a
    let Qk := modulesPseudofunctor.toDescentData Uk.f
    let Ql := modulesPseudofunctor.toDescentData Ul.f
    (∃ r : (Qk.obj ((tensorPullback q).obj F)).obj a ⟶
        (Qk.obj ((tensorPullback q).obj G)).obj a,
      tk.inv.app _ ≫ (pullback (Scheme.Cover.pullbackHom Uk pk a)).map r ≫ tk.hom.app _ =
        (pullback (Vk.f a)).map (ek.inv.app F ≫ φ ≫ ek.hom.app G)) →
    ∃ r : (Ql.obj ((tensorPullback v).obj F)).obj a ⟶
        (Ql.obj ((tensorPullback v).obj G)).obj a,
      tl.inv.app _ ≫ (pullback (Scheme.Cover.pullbackHom Ul pl a)).map r ≫ tl.hom.app _ =
        (pullback (Vl.f a)).map (el.inv.app F ≫ φ ≫ el.hom.app G) := by
  intro Uk Ul Vk Vl ek el tk tl Qk Ql
  let D := pullback d
  let Pk := pullback (Scheme.Cover.pullbackHom Uk pk a)
  let Pl := pullback (Scheme.Cover.pullbackHom Ul pl a)
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
    (tensorPullback pk) (pullback (Uk.f a)) Pk Rk ek tk
  let cl := moduleRecoveryComparisonIso (tensorPullback h) (tensorPullback v)
    (tensorPullback pl) (pullback (Ul.f a)) Pl Rl el tl
  intro hr
  obtain ⟨r, hr⟩ := hr
  change tk.inv.app _ ≫ Pk.map r ≫ tk.hom.app _ =
    Rk.map (ek.inv.app F ≫ φ ≫ ek.hom.app G) at hr
  have coherence (M : X.Modules) :
      Zf.map (ck.hom.app M) ≫ delta.hom.app (Lk.obj M) ≫
        Pl.map (alpha.inv.app M) = beta.hom.app ((tensorPullback h).obj M) ≫
          cl.hom.app M := by
    exact @openCover_tensor_comparison_coherence X Y Z W
      q v h pk pl wk wl U a d hd z hz hz0 M
  refine ⟨alpha.hom.app F ≫ D.map r ≫ alpha.inv.app G, ?_⟩
  exact transport_recovery (tensorPullback h) (tensorPullback q) (tensorPullback v)
    (tensorPullback pk) (tensorPullback pl) (pullback (Uk.f a)) (pullback (Ul.f a))
    Pk Pl Rk Rl D Zf ek el tk tl alpha beta delta coherence φ r hr

end Scheme.Modules

attribute [local instance_reducible] Scheme.Modules.moduleBaseChange

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- A chart lift at a supplied stage persists at every later stage. This is
functorial transport only: no finite-presentation, affine-chart, directedness,
affine-limit or limit-universal-property hypothesis is assumed.
Source: Stacks Project, Tags 0095, 0096 and 01ZR, first proof.
(blueprint: lem-pc-open-cover-map-lift-transport).

Proof: Fix a later stage l with j ≤ l and k ≤ l. In the category over Spec R(i),
form q:Tk → Tj, s:Tl → Tk and v:Tl → Tj from the ring-system maps. The ring
functor composition law and Spec.map_comp give s ≫ q = v. Write pk, pl and h
for the cone projections to Tk, Tl and Tj over Spec R(i). Cone naturality gives
pl ≫ s = pk, pk ≫ q = h and pl ≫ v = h. Applying baseChangeMap f yields the
same triangles for the fibre-product schemes.
Let Uk and Ul be the pulled-back covers. Cartesian chart squares give a map
d:Ul.X(a) → Uk.X(a) with d ≫ Uk.f(a) = Ul.f(a) ≫ baseChangeMap(f,s), and
 d ≫ Uj.pullbackHom(baseChangeMap(f,q),a) =
 Uj.pullbackHom(baseChangeMap(f,v),a).
Pull back the supplied chart map rk along d. Restriction of moduleBaseChange(f,v)
is canonically isomorphic to d-pullback of restriction of moduleBaseChange(f,q),
by tensor-to-ordinary pullback comparison, pullback composition and the first
triangle. Conjugating d-pullback(rk) by this comparison gives the required rl.
At the cone vertex the two iterated pulled-back charts are canonically isomorphic
by cartesian pasting. Their refinement triangle follows from pl ≫ s = pk.
Pull rk's recovery equation back along this refinement. Naturality moves each
comparison through rk; associativity identifies the remaining comparisons with
the ones for pl and v. These comparisons are mates of the same pushforward
composition isomorphisms under the pinned adjunctions, so pushforward
associativity establishes their coherence. Thus rl has the displayed recovery
equation. The supplied recovery assertion, not finite presentation or the limit
property, is the only input concerning φ. Empty charts, zero modules, identity
transitions and equivalent indices of the preorder are all included. -/
theorem openCover_map_lift_transport
    {I : Type u} [Preorder I]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec))
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj)
    (Uj : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : Uj.I₀) (k : I) (hjk : j ≤ k) :
    (let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
            (Over.homMk (Spec.map (R.map (homOfLE hjk)))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (Over.homMk (Spec.map (R.map (homOfLE hjk)))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjk))))).OpenCover.{u} := Uj.pullback₁ q
      let e := Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
              (Over.homMk (Spec.map (R.map (homOfLE hjk)))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjk).op)
      let Q := modulesPseudofunctor.toDescentData U.f
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
      let V := U.pullback₁ p
      ∃ r : (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
        let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
        t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
          (U.pullbackHom p a)).map r ≫ t.hom.app (A.obj Gj) =
        (Scheme.Modules.pullback (V.f a)).map
          (e.inv.app Fj ≫ φ ≫ e.hom.app Gj)) →
    ∀ (j' : I) (hjj' : j ≤ j'), k ≤ j' →
      let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
      let q := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE hij))))
        (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (Over.homMk (Spec.map (R.map (homOfLE hjj')))
          (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
      let U : (pullback f (Spec.map
        (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u} := Uj.pullback₁ q
      let e := Scheme.Modules.tensorPullbackCompositionIso
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (Over.homMk (Spec.map (R.map (homOfLE hjj')))
                (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)))
            (baseChangeMap f
              (T := Over.mk (Spec.map (R.map (homOfLE hij))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)))
            (by
              rw [← baseChangeMap_comp]
              congr 1
              ext
              simpa using c.w (homOfLE hjj').op)
      let Q := modulesPseudofunctor.toDescentData U.f
      let p := baseChangeMap f
        (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
        (T' := Over.mk (c.π.app (op i)))
        (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
      let V := U.pullback₁ p
      ∃ r : (Q.obj (A.obj Fj)).obj a ⟶ (Q.obj (A.obj Gj)).obj a,
        let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
        t.inv.app (A.obj Fj) ≫ (Scheme.Modules.pullback
          (U.pullbackHom p a)).map r ≫ t.hom.app (A.obj Gj) =
        (Scheme.Modules.pullback (V.f a)).map
          (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) := by
  set_option backward.isDefEq.respectTransparency false in
  set_option backward.isDefEq.respectTransparency.types false in
    intro hr l hjl hkl
    let q := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (Over.homMk (Spec.map (R.map (homOfLE hjk)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let v :
        (pullback f (Spec.map (R.map (homOfLE (hij.trans hjl))))) ⟶
          (pullback f (Spec.map (R.map (homOfLE hij)))) := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
      (Over.homMk (Spec.map (R.map (homOfLE hjl)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    let h :
        (pullback f (NatTrans.app c.π (op i))) ⟶
          (pullback f (Spec.map (R.map (homOfLE hij)))) := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
    let pk :
        (pullback f (NatTrans.app c.π (op i))) ⟶
          (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
    let pl :
        (pullback f (NatTrans.app c.π (op i))) ⟶
          (pullback f (Spec.map (R.map (homOfLE (hij.trans hjl))))) := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
      (T' := Over.mk (c.π.app (op i)))
      (Over.homMk (c.π.app (op l)) (c.w (homOfLE (hij.trans hjl)).op))
    let s :
        (pullback f (Spec.map (R.map (homOfLE (hij.trans hjl))))) ⟶
          (pullback f (Spec.map (R.map (homOfLE (hij.trans hjk))))) := baseChangeMap f
      (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
      (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjl)))))
      (Over.homMk (Spec.map (R.map (homOfLE hkl)))
        (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
    have ws : s ≫ q = v := by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      change Spec.map (R.map (homOfLE hkl)) ≫ Spec.map (R.map (homOfLE hjk)) =
        Spec.map (R.map (homOfLE hjl))
      rw [← Spec.map_comp, ← R.map_comp]
      rfl
    have wk : pk ≫ q = h := by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      change c.π.app (op k) ≫ Spec.map (R.map (homOfLE hjk)) = c.π.app (op j)
      simpa using c.w (homOfLE hjk).op
    have wl : pl ≫ v = h := by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      change c.π.app (op l) ≫ Spec.map (R.map (homOfLE hjl)) = c.π.app (op j)
      simpa using c.w (homOfLE hjl).op
    have wp : pl ≫ s = pk := by
      rw [← baseChangeMap_comp]
      congr 1
      ext
      change c.π.app (op l) ≫ Spec.map (R.map (homOfLE hkl)) = c.π.app (op k)
      simpa using c.w (homOfLE hkl).op
    let Uk := Uj.pullback₁ q
    let Ul := Uj.pullback₁ v
    let Vk := Uk.pullback₁ pk
    let Vl := Ul.pullback₁ pl
    let d : Ul.X a ⟶ Uk.X a := Limits.pullback.lift
      (Ul.f a ≫ s) (Uj.pullbackHom v a)
      (by rw [Category.assoc, ws, Uj.pullbackHom_map])
    have hd : d ≫ Uj.pullbackHom q a = Uj.pullbackHom v a :=
      Limits.pullback.lift_snd ..
    have hd0 : d ≫ Uk.f a = Ul.f a ≫ s := Limits.pullback.lift_fst ..
    let z : Vl.X a ⟶ Vk.X a :=
      Limits.pullback.lift (Vl.f a) (Scheme.Cover.pullbackHom Ul pl a ≫ d) (by
        rw [Category.assoc, hd0, ← Category.assoc, Scheme.Cover.pullbackHom_map Ul,
          Category.assoc, wp])
    have hz : z ≫ Scheme.Cover.pullbackHom Uk pk a = Scheme.Cover.pullbackHom Ul pl a ≫ d :=
      Limits.pullback.lift_snd ..
    have hz0 : z ≫ Vk.f a = Vl.f a := Limits.pullback.lift_fst ..
    let φ' : (Scheme.Modules.tensorPullback h).obj Fj ⟶
        (Scheme.Modules.tensorPullback h).obj Gj := φ
    set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      with_implicit
        have transport := @Scheme.Modules.transport_chart_map
          _ _ _ _ q v h pk pl wk wl Uj a d hd z hz hz0 Fj Gj φ'
        have result := transport (by
          exact hr)
        exact result

end AlgebraicGeometry
