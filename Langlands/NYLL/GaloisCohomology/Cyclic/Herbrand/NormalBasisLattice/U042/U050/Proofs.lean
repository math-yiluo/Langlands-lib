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

import Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.NormalBasisLattice.U042.Statements

namespace Langlands.NYLL.CyclicCohomology

noncomputable section

universe u

open scoped ValuativeRel
open Filter LocalFieldTheory

variable (K L : Type u) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
variable [ValuativeRel K]
variable [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable [ValuativeRel L]
  [Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]

omit [FiniteDimensional K L] [IsGalois K L] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] in
@[simp]
theorem mem_maximalIdealFieldSubmodule_iff (x : L) :
    mem_maximalIdealFieldSubmodule_iffStatement K L x :=
  Iff.rfl

end
end Langlands.NYLL.CyclicCohomology
