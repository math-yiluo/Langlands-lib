/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the statement of M093.024 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and place all ten source term binders of
normQuotientMapOfLE_normClass inside a closed Prop-valued definition,
preserving their order, binder kinds, shared universe u and equation.
Import only the published U023 Definitions module. Omit the source proof,
simp attribute, noncomputable section, unused universe v and all other
declarations. The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U023.Definitions

/-!
# Inclusion-induced norm quotient maps on representatives

The closed proposition states that the map induced by inclusion of actual
norm image subgroups sends a canonical class to the class of the same unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The quotient map induced by inclusion of norm subgroups preserves representatives. -/
def NormQuotientMapOfLENormClassStatement : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L ≤ localNormSubgroup K M) (x : Kˣ),
    normQuotientMapOfLE K L M h (normClass K L x) = normClass K M x

end Langlands.NYLL.LocalFieldTheory
