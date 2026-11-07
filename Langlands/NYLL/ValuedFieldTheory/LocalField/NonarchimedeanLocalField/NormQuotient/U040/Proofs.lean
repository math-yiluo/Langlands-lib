/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 6 November 2026 UTC:
Extract only the proof of M093.040 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U040 Statements module.
Prove its closed proposition by introducing the eight internal binders,
then retain the original reverse use of normClass_eq_iff_div_mem and
the norm-image membership MonoidHom.mem_range.mpr (h (x / y)).
Preserve shared universe u, the named hypothesis h and explicit x and y.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U040.Statements

/-!
# Equal norm classes under a surjective unit norm

The exact proof of the published closed assertion: surjectivity of the
actual unit norm makes the canonical norm classes of any two base-field
units equal.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- If the unit norm is surjective, all base-field units have the same norm class. -/
theorem normClass_eq_all_of_normUnits_surjective :
    NormClassEqAllOfNormUnitsSurjectiveStatement.{u} := by
  intro K L _ _ _ h x y
  apply (normClass_eq_iff_div_mem K L x y).2
  exact MonoidHom.mem_range.mpr (h (x / y))

end Langlands.NYLL.LocalFieldTheory
