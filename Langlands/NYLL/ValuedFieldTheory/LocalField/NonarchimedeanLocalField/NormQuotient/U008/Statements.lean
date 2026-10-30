/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 30 October 2026:
Extract the conclusion of M093.008 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, package all source term binders inside a closed Prop-valued
definition with their source binder kinds, import the published U007 module
alone, and omit the source proof, simp registration and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U007.Definitions

/-!
# Evaluation of a norm-quotient lift on norm classes

The closed proposition that a homomorphism descended through the norm
quotient agrees with the original homomorphism on representatives.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- A homomorphism descended through the norm quotient sends the norm class of
every unit to the value of the original homomorphism, for fields in one
arbitrary universe and a target group in an independent arbitrary universe. -/
def NormQuotientLiftNormClassStatement : Prop :=
  ∀ {K L : Type u} {M : Type v} [Field K] [Field L] [Algebra K L] [Group M]
    (f : Kˣ →* M) (h : localNormSubgroup K L ≤ f.ker) (x : Kˣ),
    normQuotientLift f h (normClass K L x) = f x

end Langlands.NYLL.LocalFieldTheory
