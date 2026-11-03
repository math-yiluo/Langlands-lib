/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 3 November 2026:
Extract only the proof of M093.031 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and import only the published U031 Statements module.
Prove its closed proposition by introducing the seven internal binders
before retaining the original membership rewrite and witness symmetry proof.
Preserve the shared universe u, both implications, the extension-unit witness
and the equation with x / y on the left. Omit the original noncomputable
section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U031.Statements

/-!
# Equal norm classes and unit-norm ratios

The exact proof of the published closed assertion: two base-field units have
the same norm class exactly when their ratio is a unit norm.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
theorem normClass_eq_iff_exists_norm_div : NormClassEqIffExistsNormDivStatement.{u} := by
  intro K L _ _ _ x y
  rw [normClass_eq_iff_div_mem K L x y]
  change x / y ∈ (normUnits K L).range ↔ _
  rw [MonoidHom.mem_range]
  constructor
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩
  · rintro ⟨z, hz⟩
    exact ⟨z, hz.symm⟩

end Langlands.NYLL.LocalFieldTheory
