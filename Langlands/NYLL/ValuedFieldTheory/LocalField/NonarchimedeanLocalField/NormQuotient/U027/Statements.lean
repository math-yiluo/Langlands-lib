/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the assertion of M093.027 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package the original three binders inside a closed
Prop-valued definition. Import only the published U026 Proofs module,
preserving its entire public chain and the existing NormQuotient,
normQuotientCommGroup, localNormSubgroup and normUnits declarations.
Retain the sole universe u and canonical self-algebra; omit the original
proof, noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U026.Proofs

/-!
# Norm classes for the identity extension

The closed assertion that every norm class for the identity extension is
the identity of the actual norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Every norm class for the identity extension is the identity. -/
def NormQuotientSelfEqOneStatement : Prop :=
  ∀ (K : Type u) [Field K] (x : NormQuotient K K), x = 1

end Langlands.NYLL.LocalFieldTheory
