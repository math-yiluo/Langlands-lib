/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Adapted by Worker 642 from NYLL commit fbd320cd8b1b06487c58227e92eb135794267709,
NormalBasisLattice.lean, lines 1647–1655. Namespace and imports are adapted;
the theorem is typed against the published Prop target. See the paired Markdown
for proof modifications. The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U060.Statements

namespace Langlands.NYLL.CyclicCohomology

open scoped ValuativeRel

universe u

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel L]

open LocalFieldTheory

omit [FiniteDimensional K L] [IsGalois K L] [ValuativeRel L] in
private theorem scaledSucc_le_local (n : Nat) (N : Submodule 𝒪[K] L) :
    chosenBaseUniformizerPowSubmodule K L (n + 1) N ≤
      chosenBaseUniformizerPowSubmodule K L n N := by
  intro z hz
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (n + 1)) * y = z at hz
  rcases hz with ⟨y, hy, rfl⟩
  change ∃ t : L, t ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * t =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (n + 1)) * y
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K) * y, ?_, ?_⟩
  · simpa only [Algebra.smul_def] using N.smul_mem (chosenIntegerRingUniformizer K) hy
  · simp only [pow_succ, map_mul, mul_assoc]

theorem chosenNormalBasisPrincipalUnitSet_succ_subset (n : Nat) :
    chosenNormalBasisPrincipalUnitSet_succ_subsetStatement K L n := by
  intro u hu
  exact scaledSucc_le_local K L n (chosenNormalBasisIntegerLattice K L) hu

end Langlands.NYLL.CyclicCohomology
