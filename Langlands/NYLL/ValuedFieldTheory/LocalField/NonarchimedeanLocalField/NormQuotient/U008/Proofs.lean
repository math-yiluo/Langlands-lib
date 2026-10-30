/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1078, 30 October 2026:
Extract the proof of M093.008 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing its
ten internal binders and applying Mathlib's QuotientGroup.lift_mk in place of
the original rfl. Import only the published U008 Statements module; omit the
source simp registration and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U008.Statements

/-!
# Evaluation of a norm-quotient lift on norm classes

Proof of the published closed proposition that a homomorphism descended
through the norm quotient agrees with the original homomorphism on
representatives.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u v

/-- A homomorphism descended through the norm quotient agrees with the original homomorphism on
representatives. -/
theorem normQuotientLift_normClass :
    NormQuotientLiftNormClassStatement.{u, v} := by
  intro K L M _ _ _ _ f h x
  exact QuotientGroup.lift_mk (localNormSubgroup K L) h x

end Langlands.NYLL.LocalFieldTheory
