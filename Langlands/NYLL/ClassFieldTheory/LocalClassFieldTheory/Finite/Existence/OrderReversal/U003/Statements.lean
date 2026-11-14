/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modified by Worker 547, 14 November 2026: extract the complete type of
M402.003 from OrderReversal.lean, lines 85–93, at upstream commit
fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL and universally close the source telescope in a Prop-valued
definition with the Statement suffix. Omit the proof at lines 94–127 and
replace the source imports with the published norm-subgroup definition
and Mathlib's existing abelian Galois and local-field classes.
Disable the unused-variable linter only for the definition to retain `h`.
See the paired Markdown for all changes.
The original LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U001.Definitions
import Mathlib.FieldTheory.Galois.Abelian
import Mathlib.NumberTheory.LocalField.Basic

/-!
# Extension embedding from reverse norm inclusion: proposition target

Source: M402.003, lines 85–127 of
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/OrderReversal.lean`.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

open LocalFieldTheory

set_option linter.unusedVariables false in
/-- Reverse inclusion of ordinary norm subgroups produces an embedding of
finite abelian extensions over the common local base field. -/
def nonempty_algHom_of_normSubgroup_leStatement : Prop :=
  ∀ (K L M : Type) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    [FiniteDimensional K L] [FiniteDimensional K M]
    [IsAbelianGalois K L] [IsAbelianGalois K M]
    [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K]
    (h : localNormSubgroup K M ≤ localNormSubgroup K L),
    Nonempty (L →ₐ[K] M)

end Langlands.NYLL.LocalClassFieldTheory
