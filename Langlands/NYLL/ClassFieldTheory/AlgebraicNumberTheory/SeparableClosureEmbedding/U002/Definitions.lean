/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Mathlib.FieldTheory.IsSepClosed

/-!
# A chosen embedding into the separable closure

Adapted by Worker 169 from NYLL M001.002 at commit
fbd320cd8b1b06487c58227e92eb135794267709,
`Nyll/ClassFieldTheory/AlgebraicNumberTheory/SeparableClosureEmbedding.lean`,
lines 57–66. See the paired Markdown for attribution and the modification record.
-/

noncomputable section

namespace Langlands.NYLL.AlgebraicNumberTheory

universe u v

variable (K : Type u) (L : Type v) [Field K] [Field L] [Algebra K L]
  [Algebra.IsSeparable K L]

/-- A chosen embedding of a separable extension into the separable closure of
its base field. -/
noncomputable def separableEmbeddingIntoSeparableClosure :
    L →ₐ[K] SeparableClosure K :=
  IsSepClosed.lift

end Langlands.NYLL.AlgebraicNumberTheory
