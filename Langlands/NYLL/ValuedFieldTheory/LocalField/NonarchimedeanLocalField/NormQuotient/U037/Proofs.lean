/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 5 November 2026 UTC:
Extract only the proof of M093.037 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U037 Statements module.
Prove its closed proposition by introducing all seven internal binders
before the original simpa using the inherited U019 division-form theorem.
Preserve shared universe u, explicit representatives x y and x * y⁻¹
with x as the left factor. Omit the source noncomputable section,
unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U037.Statements

/-!
# Equality of norm classes and multiplication by an inverse

Two base-field units have equal norm classes exactly when the first
times the inverse of the second belongs to the actual unit-norm image.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when one representative times the other's inverse is a local
norm. -/
theorem normClass_eq_iff_mul_inv_mem : NormClassEqIffMulInvMemStatement.{u} := by
  intro K L _ _ _ x y
  simpa [div_eq_mul_inv] using normClass_eq_iff_div_mem K L x y

end Langlands.NYLL.LocalFieldTheory
