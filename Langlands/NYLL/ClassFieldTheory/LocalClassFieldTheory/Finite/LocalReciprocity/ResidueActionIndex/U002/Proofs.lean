/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 85, 13 November 2026:
Extract the proof of M244.002 (toDecompositionGroupOfEqTop_coe) from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/
ResidueActionIndex.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its eight binders and closing the goal with the original rfl. Import only
the published U002 Statements module; omit the source simp registration
and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.ResidueActionIndex.U002.Statements

/-!
# The whole Galois group as decomposition group: coercion

Proof of the published closed proposition that `toDecompositionGroupOfEqTop`
does not change the underlying automorphism.
-/

namespace Langlands.NYLL.LocalClassFieldTheory

universe u v

/-- The coercion of `toDecompositionGroupOfEqTop K A hA sigma` back to
`L ≃ₐ[K] L` is `sigma` (source theorem `toDecompositionGroupOfEqTop_coe`). -/
theorem toDecompositionGroupOfEqTop_coe :
    toDecompositionGroupOfEqTop_coeStatement.{u, v} := by
  intro K L _ _ _ A hA sigma
  rfl

end Langlands.NYLL.LocalClassFieldTheory
