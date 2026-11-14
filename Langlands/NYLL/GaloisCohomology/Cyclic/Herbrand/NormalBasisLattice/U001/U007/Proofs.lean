/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.007 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
  [ValuativeRel K]

/-- The chosen normal-basis integer lattice is Galois stable. -/
theorem galoisGroup_apply_mem_chosenNormalBasisIntegerLattice
    (τ : Gal(L/K)) {x : L}
    (hx : x ∈ chosenNormalBasisIntegerLattice K L) :
    galoisGroup_apply_mem_chosenNormalBasisIntegerLatticeStatement K L τ hx := by
  unfold galoisGroup_apply_mem_chosenNormalBasisIntegerLatticeStatement
  refine Submodule.span_induction
    (p := fun x _ => τ x ∈ chosenNormalBasisIntegerLattice K L)
    ?hgen ?hzero ?hadd ?hsmul hx
  · intro x hx
    rcases hx with ⟨σ, rfl⟩
    have hτ :
        τ (σ (IsGalois.normalBasis K L (1 : Gal(L/K)))) =
          IsGalois.normalBasis K L (τ * σ) := by
      rw [IsGalois.normalBasis_apply (K := K) (L := L) (τ * σ)]
      rfl
    rw [hτ]
    rw [IsGalois.normalBasis_apply]
    exact Submodule.subset_span (Set.mem_range_self (τ * σ))
  · rw [map_zero]
    exact (chosenNormalBasisIntegerLattice K L).zero_mem
  · intro x y _ _ hx hy
    simpa using
      (chosenNormalBasisIntegerLattice K L).add_mem hx hy
  · intro a x _ hx
    have ha : τ (algebraMap 𝒪[K] L a) = algebraMap 𝒪[K] L a := by
      change τ (algebraMap K L (a : K)) = algebraMap K L (a : K)
      exact τ.commutes (a : K)
    simpa [Algebra.smul_def, ha, map_mul] using
      (chosenNormalBasisIntegerLattice K L).smul_mem a hx

end
end Langlands.NYLL.CyclicCohomology
