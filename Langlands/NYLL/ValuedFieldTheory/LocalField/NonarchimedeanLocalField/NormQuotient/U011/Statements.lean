/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 1097, 30 October 2026:
Extract the conclusion of M093.011 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix, package all source term binders inside a closed Prop-valued
definition with their source binder kinds, annotate the quotient class with its
type, import the published U010 Definitions module alone, and omit the source
proof, the simp attribute, the unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U010.Definitions

/-!
# The subgroup-equality norm-quotient equivalence on representatives

The closed proposition that the equivalence from the norm quotient to the
quotient by an equal subgroup sends the norm class of a unit to the class of
the same unit.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- After identifying the norm subgroup with another subgroup, a norm class maps to the
corresponding quotient class, for fields in one arbitrary shared universe. -/
def NormQuotientEquivOfSubgroupEqNormClassStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L]
    (N : Subgroup Kˣ) (h : localNormSubgroup K L = N) (x : Kˣ),
    normQuotientEquivOfSubgroupEq K L N h (normClass K L x) =
      (QuotientGroup.mk x : Kˣ ⧸ N)

end Langlands.NYLL.LocalFieldTheory
