/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1078, 30 October 2026:
Extract the conclusion of M093.009 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, package all source term binders inside a closed Prop-valued
definition with their source binder kinds, import the published U008 Proofs
module alone, and omit the source proof and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U008.Proofs

/-!
# Surjectivity of a norm-quotient lift

The closed proposition that descending a surjective homomorphism through the
norm quotient gives a surjective homomorphism.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

-- The source hypothesis name `hf` is kept although the proposition never mentions it.
set_option linter.unusedVariables false in
/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective, for fields in one arbitrary universe and a target
group in an independent arbitrary universe. -/
def NormQuotientLiftSurjectiveStatement : Prop :=
  ∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M]
    (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) (hf : Function.Surjective f),
    Function.Surjective (normQuotientLift f h)

end Langlands.NYLL.LocalFieldTheory
