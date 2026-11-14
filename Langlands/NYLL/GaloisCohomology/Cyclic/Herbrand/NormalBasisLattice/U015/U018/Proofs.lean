/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.018 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel
open LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [ValuativeRel K]
  [TopologicalSpace K] [IsNonarchimedeanLocalField K]

/-- The chosen uniformizer-power submodules form a descending filtration. -/
theorem chosenBaseUniformizerPowSubmodule_antitone
    (N : Submodule 𝒪[K] L) {m n : Nat} (hmn : m ≤ n) :
    chosenBaseUniformizerPowSubmodule_antitoneStatement K L N hmn := by
  unfold chosenBaseUniformizerPowSubmodule_antitoneStatement
  intro x hx
  change ∃ y : L, y ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y = x at hx
  rcases hx with ⟨y, hyN, rfl⟩
  rcases Nat.exists_eq_add_of_le hmn with ⟨d, hd⟩
  change ∃ z : L, z ∈ N ∧
    algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ m) * z =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) * y
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ d) * y, ?_, ?_⟩
  · simpa [Algebra.smul_def, mul_assoc] using
      N.smul_mem (chosenIntegerRingUniformizer K ^ d) hyN
  · simp [hd, pow_add, map_mul, mul_comm, mul_left_comm]

end
end Langlands.NYLL.CyclicCohomology
