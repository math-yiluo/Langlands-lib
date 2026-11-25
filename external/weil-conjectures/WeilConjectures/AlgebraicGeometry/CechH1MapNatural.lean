/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleCechComparison
import WeilConjectures.AlgebraicGeometry.CechComparisonMapNaturality

/-! # Naturality of the first Čech-to-cohomology comparison

Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ
(blueprint: lem-sc-cech-h1-map-natural).

The canonical comparison is characterized by the existing `IsModuleCechComparison`
predicate, so its existence cannot be witnessed by an arbitrary natural homomorphism.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace AlgebraicGeometry.Scheme.Modules

/-- For every open cover of a scheme, the canonical comparison from first Čech cohomology
of an `O_X`-module to its first module cohomology exists and is natural in the module.
Source: Stacks Project, Cohomology of Sheaves, Lemma 01EQ
(blueprint: lem-sc-cech-h1-map-natural).

Proof:
Specialize `cechComparisonMapNaturality` to degree one. Choose the canonical comparison
for each module using its existence conjunct. The comparison predicate determines the
map uniquely: evaluate it at one injective resolution and cancel the resolution
identification and the invertible homology map of alpha. Apply the theorem's naturality
conjunct to these comparisons. This reuses the same injective-resolution double-complex
construction and its lift squares, without repeating them. -/
theorem cechH1Map_natural (X : Scheme.{u}) {ι : Type u} (U : ι → X.Opens)
    (hcover : iSup U = ⊤) :
    ∃ c : ∀ F : X.Modules,
        ((CategoryTheory.cechComplexFunctor U).obj F.presheafModuleCat).homology 1 ⟶
          (RingedSpace.moduleCohomology X.toRingedSpace 1).obj F,
      (∀ F : X.Modules, IsModuleCechComparison U F 1 (c F)) ∧
      ∀ (F F' : X.Modules) (φ : F ⟶ F'),
        HomologicalComplex.homologyMap ((CategoryTheory.cechComplexFunctor U).map
            ((PresheafOfModules.forgetToPresheafModuleCat
              (op ⊤) isTerminalTop.op).map φ.val)) 1 ≫ c F' =
          c F ≫ (RingedSpace.moduleCohomology X.toRingedSpace 1).map φ := by
  classical
  obtain ⟨hexists, hnatural⟩ := (cechComparisonMapNaturality X U hcover).2 1
  choose c hc using hexists
  refine ⟨c, hc, ?_⟩
  intro F F' φ
  exact hnatural F F' φ (c F) (c F') (hc F) (hc F')

end AlgebraicGeometry.Scheme.Modules
