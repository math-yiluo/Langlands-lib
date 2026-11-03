/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 248, 2 November 2026:
Extract only the asserted type of M093.031 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all seven original binders inside a closed
Prop-valued definition, preserving their order, binder kinds, the shared
universe u, the explicit units x and y, and the orientation of the
existential witness equation.
Import only the published U030 Proofs module and preserve its entire
public chain and existing norm and quotient meanings.
Defer the truth proof; install no instance or simp registration.
Omit the original noncomputable section, unused universe v and other units.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U030.Proofs

/-!
# Equal norm classes and unit-norm ratios

The closed assertion that two base-field units have the same norm class
exactly when their ratio is the actual unit norm of some extension-field
unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- Two norm classes agree exactly when their representatives differ by a unit norm. -/
def NormClassEqIffExistsNormDivStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x y : Kˣ),
    normClass K L x = normClass K L y ↔
      ∃ z : Lˣ, x / y = normUnits K L z

end Langlands.NYLL.LocalFieldTheory
