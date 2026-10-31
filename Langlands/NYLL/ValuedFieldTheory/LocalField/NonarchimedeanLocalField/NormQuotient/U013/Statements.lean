/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 30 October 2026:
Extract the statement of M093.013 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and package all ten source term binders inside a closed
Prop-valued definition, preserving their order and binder kinds. Import only
the published U012 Definitions module, remove the repeated docstring sentence,
and omit the source proof, simp attribute, unused universe v, noncomputable
section and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U012.Definitions

/-!
# Equal norm subgroups identify classes of the same representative

The closed proposition specifying the representative evaluation of the
published equivalence between norm quotients with equal norm subgroups.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- An equality of norm subgroups identifies norm classes represented by the same base-field unit. -/
def NormQuotientEquivOfNormSubgroupEqNormClassStatement : Prop :=
  ∀ (K L M : Type u) [Field K] [Field L] [Field M]
    [Algebra K L] [Algebra K M]
    (h : localNormSubgroup K L = localNormSubgroup K M) (x : Kˣ),
    normQuotientEquivOfNormSubgroupEq K L M h (normClass K L x) =
      normClass K M x

end Langlands.NYLL.LocalFieldTheory
