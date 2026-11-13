/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 346, 13 November 2026: extract the type of M402.004
(OrderReversal.lean, lines 132–140) from upstream commit
fbd320cd8b1b06487c58227e92eb135794267709; prefix the namespace with
Langlands.NYLL, write Nat for ℕ, and close the complete theorem telescope
as a Prop-valued definition with a Statement suffix. The proof is omitted
and the source imports are replaced by the published norm-image and
standard-subgroup definitions with Mathlib's abelian Galois and local field
classes. See the paired Markdown for details.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.StandardOpenSubgroups.UniformizerPrincipalSubgroup
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Standard subgroups inside finite abelian norm subgroups: proposition target

Source: M402.004, lines 132–140 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

/-- For a prescribed unit `ϖ`, the norm subgroup of a finite abelian
extension contains a standard subgroup `⟨ϖᵈ⟩ Uⁿ` for some positive
integers `d` and `n`. -/
def exists_uniformizerPrincipalSubgroup_le_normSubgroupStatement : Prop :=
  ∀ (K L : Type) [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [IsAbelianGalois K L]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (ϖ : Kˣ),
    ∃ d n : Nat, 0 < d ∧ 1 ≤ n ∧
      LocalFieldTheory.uniformizerPrincipalSubgroup K ϖ d n ≤
        localNormSubgroup K L

end Langlands.NYLL.LocalClassFieldTheory
