/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 641 on 2026-11-14: extracted this proof into the
Langlands.NYLL namespace and made its exact published Statement the theorem
type. The paired Markdown records the proof and adaptations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U015.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]

omit [FiniteDimensional K L] [IsGalois K L] in
theorem chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_le
    {N M : Submodule 𝒪[K] L} {a n : Nat}
    (h : chosenBaseUniformizerPowSubmodule K L a N ≤ M) :
    chosenBaseUniformizerPowSubmodule_add_le_chosenBaseUniformizerPowSubmodule_of_leStatement
      K L (n := n) h := by
  intro x hx
  rcases hx with ⟨y, hyN, rfl⟩
  refine ⟨algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ a) * y, ?_, ?_⟩
  · exact h ⟨y, hyN, rfl⟩
  · change algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ n) *
        (algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ a) * y) =
      algebraMap 𝒪[K] L (chosenIntegerRingUniformizer K ^ (a + n)) * y
    simp [pow_add, map_mul, mul_assoc, mul_comm]

end
end Langlands.NYLL.CyclicCohomology
