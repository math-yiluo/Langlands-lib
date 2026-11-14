/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.ClassFormation.NormalBasisGaloisAction.LatticeStabilityStatement

/-!
Modified by Worker 517: extract M145.004 from NYLL commit
fbd320cd8b1b06487c58227e92eb135794267709, adapt namespace/imports and use
its published target. The required span induction is a private helper, and
the scalar-image membership equivalence is unfolded directly. See Proofs.md.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u

open CyclicCohomology LocalFieldTheory
open scoped ValuativeRel

private theorem latticeStableForDilate
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
    (sigma : Gal(L/K)) {x : L}
    (hx : x ∈ chosenNormalBasisIntegerLattice K L) :
    sigma x ∈ chosenNormalBasisIntegerLattice K L := by
  refine Submodule.span_induction
    (p := fun x _ => sigma x ∈ chosenNormalBasisIntegerLattice K L)
    ?_ ?_ ?_ ?_ hx
  · rintro x ⟨tau, rfl⟩
    change (sigma * tau) (IsGalois.normalBasis K L (1 : Gal(L/K))) ∈
      chosenNormalBasisIntegerLattice K L
    exact Submodule.subset_span (Set.mem_range_self (sigma * tau))
  · rw [map_zero]
    exact (chosenNormalBasisIntegerLattice K L).zero_mem
  · intro x y _ _ hx hy
    simpa using (chosenNormalBasisIntegerLattice K L).add_mem hx hy
  · intro a x _ hx
    have ha : sigma (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change sigma (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact sigma.commutes (a : K)
    simpa [Algebra.smul_def, ha, map_mul] using
      (chosenNormalBasisIntegerLattice K L).smul_mem a hx

theorem galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice
    (K L : Type u) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsGalois K L]
    [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
    (n : Nat) (sigma : Gal(L/K)) {x : L}
    (hx : x ∈ chosenBaseUniformizerPowSubmodule K L n
      (chosenNormalBasisIntegerLattice K L)) :
    galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLatticeStatement
      K L n sigma hx := by
  unfold galoisGroup_apply_mem_chosenBaseUniformizerPow_chosenNormalBasisIntegerLatticeStatement
  change ∃ y : L, y ∈ chosenNormalBasisIntegerLattice K L ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = sigma x
  rcases hx with ⟨y, hy, rfl⟩
  refine ⟨sigma y, latticeStableForDilate K L sigma hy, ?_⟩
  change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * sigma y =
    sigma (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y)
  rw [map_mul]
  change
    algebraMap K L (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K)) * sigma y =
      sigma (algebraMap K L
        (((chosenIntegerRingUniformizer K ^ n : 𝒪[K]) : K))) * sigma y
  rw [sigma.commutes]

end Langlands.NYLL.LocalClassFieldTheory
