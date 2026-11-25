/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.AffineChartOrdinaryMapDescent
import WeilConjectures.AlgebraicGeometry.ChartTensorPullbackLiftTransport
import WeilConjectures.AlgebraicGeometry.Modules.FiniteDescent

/-! # A lift at one stage on one affine chart

Source: Stacks Project, Limits Tag 01ZR, affine case, and Algebra Tag 05N7 (2).
(blueprint: lem-pc-fp-one-chart-map-lift-at-stage).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

attribute [local irreducible] Scheme.Modules.tensorPullbackCompositionIso
  Scheme.Modules.openCoverTensorPullbackComparison

set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- A restricted limit morphism lifts at one stage of the affine chart system.
Source: Stacks Project, Tag 01ZR, first proof; Tag 05N7 (2).
(blueprint: lem-pc-fp-one-chart-map-lift-at-stage).

Proof: Restrict the inverse system to the upper tail of j, and pass to its
partial-order quotient. Pull back the selected affine chart along each transition
and along the limit projection. All these schemes are affine: the transitions
are base changes of morphisms between affine schemes. Their coordinate rings are
the chart ring tensored over R(j) with the stage rings, and the limit ring is the
corresponding filtered colimit, since tensor product preserves colimits.
Restrict Fj and Gj to the chart. Their global sections are finitely presented;
quasi-coherence identifies all further pullbacks with scalar extension. Under
these identifications the restricted morphism is a map between the extensions
of these two fixed modules. Apply the map clause of
ModuleCat.finitePresentation_descent_directedColimit. Transport the resulting map
back to the chart at the selected stage using the fully faithful affine module
functor. Its commuting square gives the displayed equation: the scalar-extension
composition and restriction comparisons are the same canonical adjunction mates
as the two comparisons in the statement. This asserts a lift only at that stage;
no transport to subsequent stages is included. Empty charts and zero modules
are allowed, and j makes the upper tail nonempty even when I is not assumed
nonempty separately. No finite cover or Noetherian hypothesis is used. -/
theorem finitePresentation_one_chart_map_lift_at_stage
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u})
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    (j : I) (hij : i ≤ j)
    (Fj Gj : (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
    (hF : Fj.IsFinitePresentation) (hFq : Fj.IsQuasicoherent)
    (hG : Gj.IsFinitePresentation) (hGq : Gj.IsQuasicoherent)
    (φ : (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Fj ⟶
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj Gj)
    (Uj : (pullback f (Spec.map (R.map (homOfLE hij)))).OpenCover.{u})
    (a : Uj.I₀) (ha : IsAffine (Uj.X a)) :
    ∃ (k : I) (hjk : j ≤ k),
      let A := Scheme.Modules.moduleBaseChange f
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
          (e.inv.app Fj ≫ φ ≫ e.hom.app Gj) := by
  let q₀ := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))
  let W := Uj.pullback₁ q₀
  let t₀ := Scheme.Modules.openCoverTensorPullbackComparison q₀ Uj a
  let M := (Scheme.Modules.pullback (Uj.f a)).obj Fj
  let N := (Scheme.Modules.pullback (Uj.f a)).obj Gj
  let ψ := t₀.hom.app Fj ≫ (Scheme.Modules.pullback (W.f a)).map φ ≫ t₀.inv.app Gj
  have : Fj.IsFinitePresentation := hF
  have : Gj.IsFinitePresentation := hG
  have : Fj.IsQuasicoherent := hFq
  have : Gj.IsQuasicoherent := hGq
  obtain ⟨k, hjk, s, hs⟩ := affine_chart_ordinary_map_descent
    R c hc i f j hij Uj a ha M N (by infer_instance)
      (by infer_instance) (by infer_instance)
      (by infer_instance) ψ
  refine ⟨k, hjk, ?_⟩
  let q := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE hij))))
    (T' := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl))
  let p := baseChangeMap f
    (T := Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))))
    (T' := Over.mk (c.π.app (op i)))
    (Over.homMk (c.π.app (op k)) (c.w (homOfLE (hij.trans hjk)).op))
  have w : p ≫ q = q₀ := by
    rw [← baseChangeMap_comp]
    congr 1
    ext
    simpa using c.w (homOfLE hjk).op
  let tq := Scheme.Modules.openCoverTensorPullbackComparison q Uj a
  refine ⟨tq.inv.app Fj ≫ s ≫ tq.hom.app Gj, ?_⟩
  have H₀ := chart_tensor_pullback_lift_transport q p q₀ w Uj a Fj Gj φ
  have H₁ := H₀ s
  have H := H₁ hs
  dsimp only [q, p, q₀, w, tq] at H
  dsimp only [Scheme.Modules.moduleBaseChange]
  exact H


end AlgebraicGeometry
