/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 4699, 2026-11-15: prove the published closed target of M138.029,
the theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank at lines
382–395 of Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/ResidueExtension.lean
at upstream commit fbd320cd8b1b06487c58227e92eb135794267709, under the same name
prefixed with Langlands.NYLL. The theorem's type is the published closed proposition,
so the source binders become an opening intro; the source proof (lines 394–395) is
otherwise unchanged and uses the Library proofs of M138.024 and M138.028, whose types
are closed propositions applied to K and L. The source imports are replaced by the
published statement module and those two proof modules. The retained license and
notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.InertiaDegreeProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationInertiaDegreeProof
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.ResidueExtension.RamificationResidueDegreeStatement

/-!
# Ramification index times the canonical residue degree: proof

This module proves the published closed target for NYLL M138.029.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

open scoped ValuativeRel

/-- The local ramification identity with the inertia degree rewritten as the
finite-dimensional degree of the canonical residue-field extension. This proves
the closed target for NYLL M138.029. -/
theorem maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrank :
    maximalIdeal_ramificationIdx_mul_residue_finrank_eq_finrankStatement.{u} := by
  intro K L _ _ _ _ _ _ _ _ _ _ _ _
  rw [← maximalIdeal_inertiaDeg_eq_residue_finrank K L]
  exact maximalIdeal_ramificationIdx_mul_inertiaDeg_eq_finrank K L

end Langlands.NYLL.LocalFieldTheory
