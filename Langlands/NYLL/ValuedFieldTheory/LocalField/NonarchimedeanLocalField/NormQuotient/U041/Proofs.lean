/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1766, 7 November 2026 UTC:
Extract only the proof of M093.041 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U041 Statements module.
Name its closed proposition as the entire theorem type, introduce its
eight internal binders, and retain the original quotient-membership proof.
Preserve shared universe u, the named subgroup equality h and explicit x y.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U041.Statements

/-!
# Equal norm classes when the local norm subgroup is top

The exact proof of the published closed assertion that equality of the
actual local norm subgroup with the top subgroup makes any two canonical
norm classes equal.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- If every base-field unit is a local norm, all norm classes coincide. -/
theorem normClass_eq_of_localNormSubgroup_eq_top :
    NormClassEqOfLocalNormSubgroupEqTopStatement.{u} := by
  intro K L _ _ _ h x y
  exact (normClass_eq_iff_div_mem K L x y).2 (by
    rw [h]
    exact Subgroup.mem_top (x / y))

end Langlands.NYLL.LocalFieldTheory
