/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.PullbackUnit
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapLifts
import WeilConjectures.AlgebraicGeometry.FinitePresentationLocalMapOverlapCompatibility

/-! # Local finite-presentation descent data

Source: Stacks Project, Limits, Tag 01ZR, first proof.
(blueprint: lem-pc-fp-local-map-datum).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private theorem cancel_recovery
    {C D E H : Type*} [Category C] [Category D] [Category E] [Category H]
    (A : C ⥤ D) (B : D ⥤ E) (L : C ⥤ E) (e : L ≅ A ⋙ B) (T : E ⥤ H)
    {F G : C} (φ : L.obj F ⟶ L.obj G) (α : A.obj F ⟶ A.obj G)
    (h : T.map (B.map α) = T.map (e.inv.app F ≫ φ ≫ e.hom.app G)) :
    T.map (e.hom.app F ≫ B.map α) = T.map (φ ≫ e.hom.app G) := by
  rw [T.map_comp, h, ← T.map_comp]
  simp only [Iso.hom_inv_id_app_assoc]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem local_recovery
    {X Y : Scheme.{u}} (p : Y ⟶ X) (U : X.OpenCover.{u})
    {F G : X.Modules}
    (r : ∀ a, (Scheme.Modules.pullback (U.f a)).obj F ⟶
      (Scheme.Modules.pullback (U.f a)).obj G)
    (θ : (Scheme.Modules.tensorPullback p).obj F ⟶
      (Scheme.Modules.tensorPullback p).obj G)
    (hr : ∀ a,
      let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
      t.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom p a)).map (r a) ≫
        t.hom.app G = (Scheme.Modules.pullback ((U.pullback₁ p).f a)).map θ)
    (α : F ⟶ G) (hα : ∀ a, (Scheme.Modules.pullback (U.f a)).map α = r a) :
    ∀ a, (Scheme.Modules.pullback ((U.pullback₁ p).f a)).map
        ((Scheme.Modules.tensorPullback p).map α) =
      (Scheme.Modules.pullback ((U.pullback₁ p).f a)).map θ := by
  intro a
  let t := Scheme.Modules.openCoverTensorPullbackComparison p U a
  calc
    _ = t.inv.app F ≫ (Scheme.Modules.pullback (U.pullbackHom p a)).map
        ((Scheme.Modules.pullback (U.f a)).map α) ≫ t.hom.app G := by
      have hn := t.hom.naturality α
      dsimp only [Functor.comp_map] at hn
      rw [hn, Iso.inv_hom_id_app_assoc]
    _ = _ := by rw [hα a]; exact hr a

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Local maps between fixed models descend compatibly on a cover.
Source: Stacks Project, Limits, Tag 01ZR, first proof, map descent on overlaps.
(blueprint: lem-pc-fp-local-map-datum).

Proof: Choose a finite affine cover at stage j. Descend the restrictions of the
map using Tag 05N7. Cover pairwise intersections by finitely many affine opens;
the equality clause of 05N7 makes the descended maps agree on these overlaps
at a common later stage. These local maps and overlap equations form a morphism
psi of descent data on the pulled-back stage cover U. On the limit cover, the
local maps recover the prescribed map. The associativity comparison of pullbacks
is the conjugate of pushforward composition under the canonical tensor adjunctions.
Thus any map alpha with these components satisfies the displayed equality after
restriction to the limit cover. This is a condition on local components only:
no global stage map is constructed or asserted here. Further base changes preserve
all equations. Empty opens and an empty scheme use the unique local maps.
Finite presentation supplies finite generators and relations; quasi-separatedness
supplies finite overlap covers. -/
theorem exists_finitePresentation_local_map_datum
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f] :
    (∀ (j : I) (hij : i ≤ j) (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules),
      Fj.IsFinitePresentation → Fj.IsQuasicoherent →
      Gj.IsFinitePresentation → Gj.IsQuasicoherent →
      ∀ φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj,
      ∃ (j' : I) (hjj' : j ≤ j'),
        let A := Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (Over.homMk (Spec.map (R.map (homOfLE hjj')))
              (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
        let B := Scheme.Modules.moduleBaseChange f
              (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
              (T' := Over.mk (c.π.app (op i)))
              (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op))
        ∃ e : Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op)) ≅ A ⋙ B,
          e = Scheme.Modules.tensorPullbackCompositionIso
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
              simpa using c.w (homOfLE hjj').op) ∧
        ∃ U : (pullback f (Spec.map (R.map (homOfLE (hij.trans hjj'))))).OpenCover.{u},
          Finite U.I₀ ∧ (∀ a, IsAffine (U.X a)) ∧
          let Q := modulesPseudofunctor.toDescentData U.f
          let V := U.pullback₁ (baseChangeMap f
            (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjj')))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j')) (c.w (homOfLE (hij.trans hjj')).op)))
          ∃ ψ : Q.obj (A.obj Fj) ⟶ Q.obj (A.obj Gj),
            ∀ α : A.obj Fj ⟶ A.obj Gj, Q.map α = ψ →
              ∀ a, (Scheme.Modules.pullback (V.f a)).map (e.hom.app Fj ≫ B.map α) =
                (Scheme.Modules.pullback (V.f a)).map (φ ≫ e.hom.app Gj)) := by
  classical
  intro j hij Fj Gj hF hFq hG hGq φ
  obtain ⟨k, hjk, hk⟩ := exists_finitePresentation_local_map_lifts
    R c hc i f j hij Fj Gj hF hFq hG hGq φ
  extract_lets (descend := false) A₀ B₀ at hk
  rcases hk with ⟨e₀, he₀, U₀, hfinite, haffine, r₀, hr₀⟩
  obtain ⟨l, hkl, hl⟩ := finitePresentation_local_maps_eventually_compatible
    R c hc i f j hij Fj Gj hF hFq hG hGq φ k hjk
    e₀ he₀ U₀ hfinite haffine r₀ hr₀
  extract_lets (descend := false) hjl A B e q z U Q p V r at hl
  rcases hl with ⟨haffine', ⟨ψ, hψ⟩, hr⟩
  refine ⟨l, hjl, e, rfl, U, hfinite, haffine', ψ, ?_⟩
  intro α hα a
  have hcomponents : ∀ b, (Scheme.Modules.pullback (U.f b)).map α = r b := by
    intro b
    exact (congrArg (fun β ↦ β.hom b) hα).trans (hψ b)
  apply cancel_recovery (F := Fj) (G := Gj) A B _ e
    (Scheme.Modules.pullback (V.f a)) φ α
  exact local_recovery (F := A.obj Fj) (G := A.obj Gj) p U r
    (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) hr α hcomponents a

end AlgebraicGeometry
