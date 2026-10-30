/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 29 October 2026:
Extract the proof of M093.006 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed statement by introducing its
six internal binders before the original rfl proof. Import only the published
U006 Statements module; omit the source simp registration, unused universe v
and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U006.Statements

/-!
# Concrete evaluation of a norm class

Proof of the published closed proposition for the canonical norm class and
its concrete quotient representation.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The concrete quotient equivalence sends a norm class to the quotient class of its
representative. -/
theorem normQuotientConcreteEquiv_normClass :
    NormQuotientConcreteEquivNormClassStatement.{u} := by
  intro K L _ _ _ x
  rfl

end Langlands.NYLL.LocalFieldTheory
