/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1153, 1 November 2026:
Extract the statement of M093.019 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and place all seven source term binders of
normClass_eq_iff_div_mem inside a closed Prop-valued definition,
preserving their order, binder kinds, shared universe u and conclusion.
Import only the published U018 Proofs module. Omit the source proof,
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U018.Proofs

/-!
# Equality of norm classes

The closed proposition that two base-field units have equal norm classes
exactly when their quotient belongs to the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two units have the same norm class exactly when their quotient is a local norm. -/
def NormClassEqIffDivMemStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
    normClass K L x = normClass K L y ↔ x / y ∈ localNormSubgroup K L

end Langlands.NYLL.LocalFieldTheory
