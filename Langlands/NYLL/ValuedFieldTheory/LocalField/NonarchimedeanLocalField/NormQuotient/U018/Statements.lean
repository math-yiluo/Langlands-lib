/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 31 October 2026:
Extract the statement of M093.018 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all six source term binders of the
theorem normClass_eq_one_iff inside a closed Prop-valued definition,
preserving their order, binder kinds and shared universe u. Import only
the published U017 Proofs module and omit the source proof, noncomputable
section and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U017.Proofs

/-!
# Identity norm classes

The closed proposition stating that a base-field unit has the identity
class in the norm quotient exactly when it is the norm of an
extension-field unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- A base-field unit has trivial norm class exactly when it lies in the local norm subgroup. -/
def NormClassEqOneIffStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    normClass K L x = 1 ↔ ∃ y : Lˣ, normUnits K L y = x

end Langlands.NYLL.LocalFieldTheory
