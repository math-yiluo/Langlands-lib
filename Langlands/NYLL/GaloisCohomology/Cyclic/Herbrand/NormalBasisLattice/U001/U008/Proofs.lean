/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 516 on 2026-11-14: ported M144.008 to the
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

/-- The chosen normal-basis integer lattice is finitely generated. -/
theorem chosenNormalBasisIntegerLattice_fg :
    chosenNormalBasisIntegerLattice_fgStatement K L := by
  unfold chosenNormalBasisIntegerLattice_fgStatement
  dsimp [chosenNormalBasisIntegerLattice]
  exact Submodule.fg_span (Set.finite_range _)

end
end Langlands.NYLL.CyclicCohomology
