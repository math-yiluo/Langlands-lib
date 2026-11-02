/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 1 November 2026:
Extract only the asserted type of M093.030 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition, preserving their order, binder kinds, the shared
universe u, the explicit unit x and the explicit integer exponent n.
Import only the published U029 Proofs module and preserve its entire
public chain and existing norm and quotient meanings.
Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U029.Proofs

/-!
# Integer powers of unit norms have trivial norm class

The closed assertion that every integer power of the actual unit norm of an
extension-field unit maps to the identity under the canonical norm-quotient
projection.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- An integral power of a unit norm has trivial norm class. -/
def NormClassNormUnitsZpowEqOneStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Lˣ) (n : Int),
    normClass K L ((normUnits K L x) ^ n) = 1

end Langlands.NYLL.LocalFieldTheory
