/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the assertion of M093.025 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package the original three binders inside a closed
Prop-valued definition. Import only the published U024 Proofs module,
retaining the predecessor chain and the existing normUnits definition.
Retain the sole universe u and canonical self-algebra; omit the original
proof, noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U024.Proofs

/-!
# Unit norm for the identity extension

The closed assertion that the unit norm of a field over itself fixes each unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Over the identity extension, the unit norm fixes every base-field unit. -/
def NormUnitsSelfApplyStatement : Prop :=
  ∀ (K : Type u) [Field K] (x : Kˣ), normUnits K K x = x

end Langlands.NYLL.LocalFieldTheory
