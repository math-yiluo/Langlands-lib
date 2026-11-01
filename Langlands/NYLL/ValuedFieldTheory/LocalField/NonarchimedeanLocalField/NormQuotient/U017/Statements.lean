/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 31 October 2026:
Extract the statement of M093.017 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all six source term binders of the
theorem mk_normUnits_eq_one inside a closed Prop-valued definition,
preserving their order, binder kinds and shared universe u. Import only
the published U016 Proofs module and omit the source proof, noncomputable
section and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U016.Proofs

/-!
# Norm classes of extension-unit norms

The closed proposition stating that the norm of every extension-field unit
has the identity class in the norm quotient.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The quotient class of any extension-unit norm is the identity norm class. -/
def MkNormUnitsEqOneStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ),
    normClass K L (normUnits K L x) = 1

end Langlands.NYLL.LocalFieldTheory
