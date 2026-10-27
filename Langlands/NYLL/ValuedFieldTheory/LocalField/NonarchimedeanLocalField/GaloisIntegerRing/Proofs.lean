/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.GaloisIntegerRing.Statements

/-!
# Evaluation of restriction to an integral-closure valuation ring

Adapted by Worker 382 from NYLL M139.003–004 on 27 October 2026.
The namespace is prefixed by `Langlands.NYLL`; each theorem proves its published
closed statement target over an arbitrary universe. The source proofs `rfl` are
replaced by Mathlib's `algebraMap_galRestrict'_apply`, matching the published
`galRestrict'` definition. The `@[simp]` attributes are not retained.
See the paired Markdown for correspondence and attribution.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The forward restriction has the same ambient-field value as the supplied
field automorphism. This proves the closed statement target for NYLL M139.003. -/
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_apply :
    GaloisGroupIntegerRingEquivOfIsIntegralClosureApplyStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ x
  exact algebraMap_galRestrict'_apply 𝒪[K] 𝒪[L] 𝒪[L] σ.toAlgHom x

/-- The inverse restriction has the same ambient-field value as the inverse
field automorphism. This proves the closed statement target for NYLL M139.004. -/
theorem galoisGroupIntegerRingEquivOfIsIntegralClosure_symm_apply :
    GaloisGroupIntegerRingEquivOfIsIntegralClosureSymmApplyStatement.{u} := by
  intro K L _ _ _ _ _ _ _ σ x
  exact algebraMap_galRestrict'_apply 𝒪[K] 𝒪[L] 𝒪[L] σ.symm.toAlgHom x

end Langlands.NYLL.LocalFieldTheory
