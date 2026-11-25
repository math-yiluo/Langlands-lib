/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.AlgebraicGeometry.TensorPullbackCompositionIso
public import WeilConjectures.AlgebraicGeometry.OpenCoverTensorPullbackComparison
import WeilConjectures.AlgebraicGeometry.FinitePresentationOneChartMapLiftAtStage
import WeilConjectures.AlgebraicGeometry.OpenCoverMapLiftTransport

/-! # Eventual lifting of a map on one affine chart
Source: Stacks Project, Limits Tag 01ZR and Algebra Tag 05N7 (2).
(blueprint: lem-pc-fp-one-chart-map-lift).
-/

@[expose] public section
universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry

-- The unchanged statement has an unused witness proof and an unused intermediate functor.
set_option linter.unusedVariables false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Lifting on a single supplied affine chart persists at every later stage.
No finiteness of the supplied cover is assumed; only the selected chart is affine.
Source: Stacks Project, Limits Tag 01ZR, first proof; Algebra Tag 05N7 (2).
(blueprint: lem-pc-fp-one-chart-map-lift).

Proof: The inverse images of the selected affine chart are affine because the
transition maps are base changes of maps between affine schemes. Their rings form
the filtered colimit obtained by tensoring the chart ring with the base-ring system
on the upper tail of j. Pass through the partial-order quotient of the preorder.
Quasi-coherence identifies restrictions with modules and pullback with extension
of scalars; finite presentation gives finitely presented chart modules. Apply the
map clause of ModuleCat.finitePresentation_descent_directedColimit to lift the
restricted limit map at a stage k. Extend that map by scalars at every l above k.
Transport back through the affine module equivalence. Naturality of the restriction
comparison and associativity of scalar extension give the recovery equation with
the canonical tensor composition comparison. No finite-cover choice or assembly
occurs. Empty charts and zero modules give unique maps; a singleton index set
recovers the restricted original map. No Noetherianity is needed. -/
theorem finitePresentation_one_chart_map_lift_eventually
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
    ∃ (k : I) (hjk : j ≤ k), ∀ (j' : I) (hjj' : j ≤ j'), k ≤ j' →
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
  obtain ⟨k, hjk, hstage⟩ := finitePresentation_one_chart_map_lift_at_stage
    R c hc i f j hij Fj Gj hF hFq hG hGq φ Uj a ha
  refine ⟨k, hjk, ?_⟩
  intro l hjl hkl
  set_option backward.isDefEq.respectTransparency true in
    set_option backward.isDefEq.respectTransparency.types true in
      with_reducible
        exact @openCover_map_lift_transport.{u} I inferInstance R c i Xi f j hij
          Fj Gj φ Uj a k hjk hstage l hjl hkl

end AlgebraicGeometry
