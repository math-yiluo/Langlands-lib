/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.RingTheory.Noetherian.Basic
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
import WeilConjectures.AlgebraicGeometry.BoundedGradedFamilyDescent
import WeilConjectures.AlgebraicGeometry.BoundedGradedMapCompatibility

/-! # Descent of bounded graded modules and successive maps

Source: Stacks Project, Tag 01ZR, clauses (1) and (2).
(blueprint: lem-pc-bounded-graded-module-map-descent)
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- Descend a bounded graded family and its successive maps, without imposing any
square-zero equations. Source: Stacks Project, Tag 01ZR, clauses (1) and (2).
(blueprint: lem-pc-bounded-graded-module-map-descent)

Proof: Only the degrees in the integer interval [a,b] need nonzero models. Apply
clause (1) of finitePresentation_module_map_descent to these finitely many terms.
Directedness gives a stage above i and all their stages. Pull their models to that
stage; tensor pullback preserves finite presentations and zero objects, and the
composition isomorphism identifies their further pullbacks with the original terms.
Put zero outside [a,b]. A morphism with a zero source or target is uniquely zero,
so only the adjacent pairs contained in [a,b] require descending a map. Transport
those maps through the chosen term isomorphisms and apply clause (2) to these fixed
models. Choose a common stage above the finitely many map stages and pull all models
and maps to it. Naturality of pullback composition preserves the prescribed map
comparisons. Extend the comparisons outside the interval by the unique isomorphisms
between zero objects. This gives all displayed equalities, including boundary maps.
There is deliberately no claim that successive maps have zero composite. If a>b,
every term is zero and stage i with the zero family suffices. -/
theorem bounded_graded_module_map_descent
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) [∀ k : I, IsNoetherianRing (R.obj k)]
    (c : Cone (R.op ⋙ Scheme.Spec)) (hc : IsLimit c) [IsAffine c.pt]
    (i : I) {Xi : Scheme.{u}} (f : Xi ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (M : ℤ → (pullback f (c.π.app (op i))).Modules)
    (a b : ℤ) (hM_zero : ∀ n : ℤ, n < a ∨ b < n → IsZero (M n))
    (hM_fp : ∀ n : ℤ, (M n).IsFinitePresentation)
    (hM_qc : ∀ n : ℤ, (M n).IsQuasicoherent)
    (d : ∀ n : ℤ, M n ⟶ M (n + 1)) :
    ∃ (j : I) (hij : i ≤ j)
      (F : ℤ → (pullback f (Spec.map (R.map (homOfLE hij)))).Modules)
      (δ : ∀ n : ℤ, F n ⟶ F (n + 1)),
      (∀ n : ℤ, n < a ∨ b < n → IsZero (F n)) ∧
      (∀ n : ℤ, (F n).IsFinitePresentation) ∧
      (∀ n : ℤ, (F n).IsQuasicoherent) ∧
      ∃ e : ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).obj (F n) ≅ M n,
        ∀ n : ℤ,
          (Scheme.Modules.moduleBaseChange f
            (T := Over.mk (Spec.map (R.map (homOfLE hij))))
            (T' := Over.mk (c.π.app (op i)))
            (Over.homMk (c.π.app (op j)) (c.w (homOfLE hij).op))).map (δ n) ≫
              (e (n + 1)).hom = (e n).hom ≫ d n := by
  classical
  obtain ⟨j, hij, F, hFz, hFfp, hFqc, ⟨e⟩⟩ :=
    bounded_graded_family_descent R c hc i f M a b hM_zero hM_fp hM_qc
  let φ := fun n ↦ (e n).hom ≫ d n ≫ (e (n + 1)).inv
  obtain ⟨k, _, hik, G, δ, hGz, hGfp, hGqc, t, ht⟩ :=
    bounded_graded_map_compatibility R c hc i f a b j hij F hFz hFfp hFqc φ
  refine ⟨k, hik, G, δ, hGz, hGfp, hGqc, fun n ↦ t n ≪≫ e n, ?_⟩
  intro n
  dsimp only [Iso.trans_hom]
  rw [← Category.assoc, ht n]
  simp [φ, Category.assoc]

end AlgebraicGeometry
