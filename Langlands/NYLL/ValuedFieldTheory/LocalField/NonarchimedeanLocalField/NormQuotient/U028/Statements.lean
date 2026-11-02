/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the asserted type of the Prop-valued instance M093.028 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package both original binders inside a closed
Prop-valued definition. Import only the published U027 Proofs module,
preserving its entire public chain and the existing NormQuotient,
normQuotientCommGroup, localNormSubgroup and normUnits declarations.
Retain the sole universe u and canonical self-algebra. Defer the truth
proof and local instance installation; install no global or scoped instance.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U027.Proofs

/-!
# Subsingleton norm quotient for the identity extension

The closed assertion that the actual norm quotient of a field over itself
is a subsingleton.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The norm quotient of a field over itself is a subsingleton. -/
def NormQuotientSelfSubsingletonStatement : Prop :=
  ∀ (K : Type u) [Field K], Subsingleton (NormQuotient K K)

end Langlands.NYLL.LocalFieldTheory
