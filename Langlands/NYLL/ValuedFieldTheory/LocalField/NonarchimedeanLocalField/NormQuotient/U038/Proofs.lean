/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 6 November 2026 UTC:
Extract only the proof of M093.038 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U038 Statements module.
Prove its closed proposition by introducing the seven internal binders
before retaining the original division-witness and cancellation proof,
with the backward implication supplied by the public U036 theorem.
Preserve the shared universe u, explicit x and y, both implications and
the extension-unit witness with x = normUnits K L z * y.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U038.Statements

/-!
# Equal norm classes and left multiplication by a unit norm

The exact proof of the published closed assertion: equal norm classes are
equivalent to a unit norm converting the second representative to the first
by multiplication on the left.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when a unit norm converts the second representative to the first
on the left. -/
theorem normClass_eq_iff_exists_norm_mul_left :
    NormClassEqIffExistsNormMulLeftStatement.{u} := by
  intro K L _ _ _ x y
  constructor
  · intro hxy
    rcases (normClass_eq_iff_exists_norm_div K L x y).1 hxy with ⟨z, hz⟩
    refine ⟨z, ?_⟩
    rw [← hz]
    exact (div_mul_cancel x y).symm
  · rintro ⟨z, hz⟩
    exact normClass_eq_of_eq_normUnits_mul K L z hz

end Langlands.NYLL.LocalFieldTheory
