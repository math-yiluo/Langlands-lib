/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 9 November 2026: extract the signatures of
M255.001–002 from Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/
NormContinuity.lean at fbd320cd8b1b06487c58227e92eb135794267709;
replace theorems with Prop-valued targets bearing the Statement suffix,
prefix the namespace with Langlands.NYLL and import only the published
normUnits definition and the original Mathlib analytic imports.
The original hypotheses and independent universes are unchanged.
LICENSE and NOTICE are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NormUnits.U002.Definitions
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Instances.Matrix

/-! # Targets for continuity of finite-dimensional field norms -/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- Target for continuity of the field norm on a finite-dimensional normed algebra. -/
def algebraNorm_continuous_of_finiteDimensionalStatement
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] : Prop :=
  Continuous (Algebra.norm K : L → K)

/-- Target for continuity of the field norm restricted to unit groups. -/
def normUnits_continuous_of_finiteDimensionalStatement
    (K : Type u) (L : Type v)
    [NontriviallyNormedField K] [NormedField L]
    [Algebra K L] [FiniteDimensional K L] [CompleteSpace K]
    [ContinuousSMul K L] : Prop :=
  Continuous (normUnits K L)

end Langlands.NYLL.LocalFieldTheory
