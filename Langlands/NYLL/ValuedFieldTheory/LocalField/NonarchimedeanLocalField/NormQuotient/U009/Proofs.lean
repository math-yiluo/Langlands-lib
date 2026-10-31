/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1078, 30 October 2026:
Extract the proof of M093.009 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing its
ten internal binders, then following the original proof unchanged. Import
only the published U009 Statements module; omit all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U009.Statements

/-!
# Surjectivity of a norm-quotient lift

Proof of the published closed proposition that descending a surjective
homomorphism through the norm quotient gives a surjective homomorphism.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- A map obtained by descending a surjective homomorphism through the norm
quotient is still surjective. -/
theorem normQuotientLift_surjective :
    NormQuotientLiftSurjectiveStatement.{u, v} := by
  intro K L M _ _ _ _ f h hf y
  obtain ⟨x, rfl⟩ := hf y
  exact ⟨normClass K L x, normQuotientLift_normClass f h x⟩

end Langlands.NYLL.LocalFieldTheory
