/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 642 (2026-11-16): extract M133.018 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/IdealQuotients.lean
at fbd320cd8b1b06487c58227e92eb135794267709; adapt namespace and imports,
state the theorem using its published Prop target, and unfold that target.
The source proof is otherwise retained. LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.UniformizerPowMap.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.IdealQuotients.U015.Proofs

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The chosen uniformizer field unit has normalized additive value negative one. -/
theorem v_integerRingUniformizerFieldUnit
    (K : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] :
    v_integerRingUniformizerFieldUnitStatement K := by
  change IsNonarchimedeanLocalField.v K
    (Additive.ofMul (integerRingUniformizerFieldUnit K)) = -1
  exact v_integerRingIrreducibleFieldUnit K
    (chosenIntegerRingUniformizer K) (chosenIntegerRingUniformizer_irreducible K)
    (integerRingUniformizerFieldUnit K) rfl

end Langlands.NYLL.LocalFieldTheory
