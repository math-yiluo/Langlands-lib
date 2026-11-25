/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesFiniteProducts
import WeilConjectures.AlgebraicGeometry.CoherentFormalModuleKernel
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCokernelClosure
import WeilConjectures.AlgebraicGeometry.CoherentFormalModulesCoimageImage

/-! # Coherent formal modules form an abelian category

Source: Stacks Project, Cohomology of Schemes, Lemma 087X, part (1), and the description
of cokernels in its proof (blueprint: lem-weil-pbc-coherent-formal-modules-abelian).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

/-- The category Coh(X,I) is abelian, and every morphism has a cokernel cofork whose
image under evaluation at each positive level is a cokernel cofork of that component.
Thus its cokernel is the inverse system of termwise cokernels, with transitions induced
by the universal property. Here `op n` denotes positive level `n + 1`.

Source: Stacks, Lemma 087X, part (1), and its proof
(blueprint: lem-weil-pbc-coherent-formal-modules-abelian).

Proof: Closure under ambient finite products supplies finite products in the full
subcategory. Extract the stabilized kernel and its unique-factorization property
from `coherentFormalModule_kernel`, and build its limiting fork. Closure under
ambient cokernels supplies cokernels and makes the inclusion preserve them.
The comparison lemma and Mathlib's coimage-image criterion give abelianness.
For the second clause take the canonical cokernel cofork. The inclusion followed
by any evaluation functor preserves its colimit, so each evaluated cofork is
colimiting. The three closure/comparison lemmas record the geometric work of
Steps 2, 3, and 8--9 of the original plan; the existing kernel theorem supplies
Steps 4--7. No termwise-kernel assertion is used.
-/
theorem coherentFormalModule_abelian (X : Scheme.{u}) [IsNoetherian X]
    (I : X.IdealSheafData) :
    Nonempty (Abelian (CoherentFormalModule X I)) ∧
      ∀ (F G : CoherentFormalModule X I) (α : F ⟶ G),
        ∃ c : CokernelCofork α, Nonempty (IsColimit c) ∧
          ∀ n : ℕ, Nonempty (IsColimit
            (((IsCoherentFormalModule I).ι ⋙
              (evaluation ℕᵒᵖ X.Modules).obj (op n)).mapCocone c)) := by
  classical
  have := coherentFormalModules_closedUnderFiniteProducts X I
  have := coherentFormalModules_closedUnderCokernels X I
  have : HasKernels (CoherentFormalModule X I) := by
    constructor
    intro F G α
    obtain ⟨_, _, _, _, _, K, ι, _, _, _, hzero, huni⟩ :=
      coherentFormalModule_kernel I F G α
    refine ⟨⟨KernelFork.ofι ι hzero, ?_⟩⟩
    exact Fork.IsLimit.mk' _ fun s ↦ Classical.choice (by
      obtain ⟨δ, hδ, hδ_unique⟩ := huni s.pt s.ι (by simp)
      exact ⟨⟨δ, hδ, fun {m} hm ↦ hδ_unique m hm⟩⟩)
  have : ∀ {F G : CoherentFormalModule X I} (α : F ⟶ G),
      IsIso (Abelian.coimageImageComparison α) := fun α ↦
    coherentFormalModules_coimageImage_isIso X I α
  refine ⟨⟨Abelian.ofCoimageImageComparisonIsIso⟩, ?_⟩
  intro F G α
  have : PreservesColimit (parallelPair α 0) (IsCoherentFormalModule I).ι :=
    (IsCoherentFormalModule I).preservesCokernels_ι α
  refine ⟨CokernelCofork.ofπ (cokernel.π α) (cokernel.condition α),
    ⟨cokernelIsCokernel α⟩, ?_⟩
  intro n
  exact ⟨isColimitOfPreserves
    ((IsCoherentFormalModule I).ι ⋙ (evaluation ℕᵒᵖ X.Modules).obj (op n))
    (cokernelIsCokernel α)⟩

end AlgebraicGeometry
