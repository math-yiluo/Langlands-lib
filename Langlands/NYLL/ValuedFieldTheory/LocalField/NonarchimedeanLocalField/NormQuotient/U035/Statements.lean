/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 5 November 2026 UTC:
Extract the asserted type of M093.035 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace with Langlands.NYLL and quantify all eight source
binders inside a closed Prop-valued definition, preserving their order,
binder kinds and shared universe u. Retain the integer exponent and
right multiplication by that power of the actual unit norm.
Use only the public U034 Proofs import and leave its full chain unchanged.
Omit the truth proof, unused universe v, noncomputable section and other
declarations; add no instance or simp registration.
The inherited LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U034.Proofs

/-!
# Right multiplication by an integer power of a unit norm

A closed assertion about the canonical projection from base-field units
to their quotient by the image of the actual algebra unit norm.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Right multiplication by an integral power of a unit norm leaves a norm class unchanged. -/
def NormClassMulNormUnitsZpowStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) (z : Lˣ) (n : Int),
    normClass K L (x * (normUnits K L z) ^ n) = normClass K L x

end Langlands.NYLL.LocalFieldTheory
