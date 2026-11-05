/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1560, 4 November 2026:
Extract the asserted type of M093.033 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709.
Prefix the namespace with Langlands.NYLL and quantify the seven source
binders inside a closed Prop-valued definition, preserving their order,
binder kinds and shared universe u. Retain multiplication by the unit norm
on the right, with the base unit x preceding the extension unit z.
Use only the public U032 Proofs import and leave its full chain unchanged.
Omit the truth proof, unused universe v, noncomputable section and other
declarations; add no instance or simp registration.
The inherited LICENSE and NOTICE remain in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U032.Proofs

/-!
# Right multiplication by a unit norm

A closed assertion about the canonical projection from base-field units
to their quotient by the image of the actual algebra unit norm.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Multiplying a representative on the right by a unit norm leaves its norm class unchanged. -/
def NormClassMulNormUnitsStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ) (z : Lˣ),
    normClass K L (x * normUnits K L z) = normClass K L x

end Langlands.NYLL.LocalFieldTheory
