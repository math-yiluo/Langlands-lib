/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 31 October 2026:
Extract the statement of M093.016 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all eight source term binders of the
protected theorem NormQuotient.inductionOn inside a closed Prop-valued
definition, preserving their order, binder kinds, shared universe u and
Prop-valued motive. Keep the hypothesis name h with the unused-variables
linter disabled for this declaration only. Import only the published U015
Proofs module and omit the source proof, protected modifier, noncomputable
section and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U015.Proofs

/-!
# Induction on norm-quotient classes

The closed proposition stating that a property of norm-quotient classes
holds for every class once it holds for the norm class of every base-field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

-- The source hypothesis name `h` is kept although the proposition never mentions it.
set_option linter.unusedVariables false in
/-- Eliminate a norm-quotient class through the canonical quotient map,
without exposing the quotient representation to clients. -/
def NormQuotientInductionOnStatement : Prop :=
  ∀ {K L : Type u} [Field K] [Field L] [Algebra K L]
    {motive : NormQuotient K L → Prop} (q : NormQuotient K L)
    (h : ∀ x : Kˣ, motive (normClass K L x)), motive q

end Langlands.NYLL.LocalFieldTheory
