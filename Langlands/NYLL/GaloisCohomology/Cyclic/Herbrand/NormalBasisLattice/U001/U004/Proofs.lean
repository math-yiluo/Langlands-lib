/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.004 to the
Langlands.NYLL namespace and proved the published Statement target.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U001.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u
open scoped ValuativeRel

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L] [ValuativeRel K]

/-- Every normal-basis vector belongs to the chosen integer lattice. -/
theorem normalBasis_mem_integerLattice (σ : Gal(L/K)) :
    normalBasis_mem_integerLatticeStatement K L σ := by
  unfold normalBasis_mem_integerLatticeStatement
  rw [IsGalois.normalBasis_apply]
  exact Submodule.subset_span (Set.mem_range_self σ)

end
end Langlands.NYLL.CyclicCohomology
