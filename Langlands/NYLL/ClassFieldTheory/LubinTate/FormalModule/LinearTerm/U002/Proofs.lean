/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 463 on 2026-11-14: extracted only the theorem M347.002
(lines 31–35) of Nyll/ClassFieldTheory/LubinTate/FormalModule/LinearTerm.lean
at commit fbd320cd8b1b06487c58227e92eb135794267709; prefixed the namespace
with Langlands.NYLL; imported the published Statements module instead of the
source imports; stated the conclusion as the published proposition
constantCoeff_linearFormStatement L, with explicit independent universes u and
v; opened it with `unfold` before the unchanged source tactic; replaced the
docstring and added a module description. The source @[simp] attribute is
retained; a one-command local reducibility override of the target proposition
makes it register the source equation. Details are in the paired Markdown;
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LubinTate.FormalModule.LinearTerm.Statements

/-!
# The linear form has zero constant coefficient (NYLL M347.002)

The multivariable linear form `∑ i, C (L i) * X i` has constant coefficient
zero, for every commutative ring and finite variable type.
-/

namespace Langlands.NYLL.LubinTate.SameUniformizer

universe u v

variable {R : Type u} [CommRing R]
variable {σ : Type v} [Fintype σ]

-- Making the target proposition reducible for this one command lets the
-- `@[simp]` attribute register the source rewrite
-- `MvPowerSeries.constantCoeff (linearForm L) = 0` rather than
-- `constantCoeff_linearFormStatement L = True`; the theorem's type is unchanged.
-- Lean requires `allowUnsafeReducibility` for a local `[reducible]` override;
-- the registered left-hand side does not mention the target proposition.
set_option allowUnsafeReducibility true in
attribute [local reducible] constantCoeff_linearFormStatement in
/-- The multivariable linear form `∑ i, C (L i) * X i` has constant
coefficient zero. -/
@[simp]
theorem constantCoeff_linearForm (L : σ → R) :
    constantCoeff_linearFormStatement L := by
  unfold constantCoeff_linearFormStatement
  simp [linearForm]

end Langlands.NYLL.LubinTate.SameUniformizer
