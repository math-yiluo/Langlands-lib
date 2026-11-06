/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1736, 6 November 2026 UTC:
Extract only the proof of M093.039 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U039 Statements module.
Prove its closed proposition by introducing the seven internal binders,
then retain the original left-factor witness, commutativity and
right-multiplication class-identity proof. Preserve shared universe u,
explicit x and y, both implications and x = y * normUnits K L z.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U039.Statements

/-!
# Equal norm classes and right multiplication by a unit norm

The exact proof of the published closed assertion: equal norm classes are
equivalent to a unit norm converting the second representative to the first
by multiplication on the right.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when a unit norm converts the second representative to the first
on the right. -/
theorem normClass_eq_iff_exists_norm_mul_right :
    NormClassEqIffExistsNormMulRightStatement.{u} := by
  intro K L _ _ _ x y
  constructor
  · intro hxy
    rcases (normClass_eq_iff_exists_norm_mul_left K L x y).1 hxy with ⟨z, hz⟩
    exact ⟨z, by simpa [mul_comm] using hz⟩
  · rintro ⟨z, hz⟩
    rw [hz]
    exact normClass_mul_normUnits K L y z

end Langlands.NYLL.LocalFieldTheory
