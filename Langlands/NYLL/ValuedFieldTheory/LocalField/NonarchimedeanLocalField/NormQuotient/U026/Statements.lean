/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract only the assertion of M093.026 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package the original two binders inside a closed
Prop-valued definition. Import only the published U025 Proofs module,
preserving its entire public chain and the existing localNormSubgroup
and normUnits definitions. Retain the sole universe u and canonical
self-algebra; omit the original proof, noncomputable section, unused
universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U025.Proofs

/-!
# Norm subgroup for the identity extension

The closed assertion that every base-field unit is a norm for the identity
extension.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- For the identity extension, every base-field unit is a norm. -/
def LocalNormSubgroupSelfStatement : Prop :=
  ∀ (K : Type u) [Field K], localNormSubgroup K K = ⊤

end Langlands.NYLL.LocalFieldTheory
