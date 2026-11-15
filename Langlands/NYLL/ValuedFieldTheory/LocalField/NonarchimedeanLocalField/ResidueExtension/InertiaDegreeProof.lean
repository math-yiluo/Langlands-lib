/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 4699, 2026-11-15: prove the published closed target of M138.024,
the theorem maximalIdeal_inertiaDeg_eq_residue_finrank at lines 308–319 of
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean at
upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name prefixed
with Langlands.NYLL. The theorem's type is the published closed proposition, so the
source binders become an opening intro; the source proof (lines 318–319) is otherwise
unchanged. The source imports are replaced by the published statement module. The
retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.InertiaDegreeStatement

/-!
# Inertia degree and the canonical residue extension: proof

This module proves the published closed target for NYLL M138.024.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The mathlib inertia degree of the maximal ideals agrees with the concrete
degree of the canonical residue-field extension supplied by a valuation
extension. This proves the closed target for NYLL M138.024. -/
theorem maximalIdeal_inertiaDeg_eq_residue_finrank :
    maximalIdeal_inertiaDeg_eq_residue_finrankStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _
  rw [Ideal.inertiaDeg_eq_of_isMaximal (𝓂[K] : Ideal 𝒪[K]) (𝓂[L] : Ideal 𝒪[L])]
  rfl

end Langlands.NYLL.LocalFieldTheory
