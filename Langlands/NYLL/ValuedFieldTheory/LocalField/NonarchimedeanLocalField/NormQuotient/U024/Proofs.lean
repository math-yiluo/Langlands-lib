/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the proof of M093.024 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing
its ten internal binders, then applying the published
normQuotientLift_normClass as in the original proof. Import only the
published U024 Statements module. Retain the sole shared universe u,
omitting the source simp registration, noncomputable section, unused
universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U024.Statements

/-!
# Inclusion-induced norm quotient maps on representatives

Proof that the named map induced by inclusion of actual norm image subgroups
sends the class of a unit to the class of the same unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The quotient map induced by inclusion of norm subgroups preserves representatives. -/
theorem normQuotientMapOfLE_normClass :
    NormQuotientMapOfLENormClassStatement.{u} := by
  intro K L M _ _ _ _ _ h x
  exact normQuotientLift_normClass (normClass K M) _ x

end Langlands.NYLL.LocalFieldTheory
