/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 202, 11 November 2026: extract M255.002 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormContinuity.lean
at fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, prove the published Statement target and import the published
M255.001 proof by Lean name. The units_map proof route, original parameters,
instances and independent universes are retained.
LICENSE and NOTICE are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.Statements
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormContinuity.U001.Proofs

/-! # Continuity of the finite-dimensional field norm on units -/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- The field norm induced on unit groups is continuous. -/
theorem normUnits_continuous_of_finiteDimensional
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] :
    normUnits_continuous_of_finiteDimensionalStatement K L := by
  change Continuous (normUnits K L)
  unfold normUnits
  exact Continuous.units_map (Algebra.norm K : L →* K)
    (algebraNorm_continuous_of_finiteDimensional K L)

end Langlands.NYLL.LocalFieldTheory
