/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the proof of the Prop-valued instance M093.028 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and prove the published closed
NormQuotientSelfSubsingletonStatement by introducing its two internal
binders. Retain the original allEq proof using the public
normQuotient_self_eq_one theorem, but publish a named theorem without
global or scoped instance registration. Import only U028.Statements
and preserve its entire public chain. Retain the sole universe u and
canonical self-algebra; omit the original noncomputable section,
unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U028.Statements

/-!
# Subsingleton norm quotient for the identity extension

Proof that any two classes in the actual identity-extension norm quotient
are equal, using their equality to the quotient identity.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The norm quotient of a field over itself is a subsingleton. -/
theorem normQuotient_self_subsingleton : NormQuotientSelfSubsingletonStatement.{u} := by
  intro K _
  exact {
    allEq := fun x y => by
      rw [normQuotient_self_eq_one K x, normQuotient_self_eq_one K y]
  }

end Langlands.NYLL.LocalFieldTheory
