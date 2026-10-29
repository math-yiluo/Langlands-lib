/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 29 October 2026:
Extract the conclusion of M093.006 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, package all source term binders inside a closed Prop-valued
definition, import the published U005 module alone, and omit the source proof,
simp registration, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions

/-!
# Concrete evaluation of a norm class

The closed proposition that the published representation equivalence sends a
canonical norm class to the concrete quotient class of its representative.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The concrete quotient equivalence sends every norm class to the quotient
class of its representative, for fields in one arbitrary universe. -/
def NormQuotientConcreteEquivNormClassStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L] (x : Kˣ),
    normQuotientConcreteEquiv K L (normClass K L x) = QuotientGroup.mk x

end Langlands.NYLL.LocalFieldTheory
