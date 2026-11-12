/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 126, 11 November 2026: extract M255.001 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the published Statement target and replace the
determinant proof body with the published module-topology continuity theorem.
The original parameters, instances and independent universes are unchanged.
LICENSE and NOTICE are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.Statements
import Langlands.Representation.Plancherel.TorusNormKernel.FieldNormCompact

/-! # Continuity of the finite-dimensional algebra norm -/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The field norm of a finite-dimensional normed algebra over a complete
nontrivially normed field is continuous. -/
theorem algebraNorm_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    algebraNorm_continuous_of_finiteDimensionalStatement K L := by
  let : IsModuleTopology K L := isModuleTopologyOfFiniteDimensional
  exact Langlands.Plancherel.TorusNormKernel.continuous_algebraNorm (F := K) (E := L)

end Langlands.NYLL.LocalFieldTheory
