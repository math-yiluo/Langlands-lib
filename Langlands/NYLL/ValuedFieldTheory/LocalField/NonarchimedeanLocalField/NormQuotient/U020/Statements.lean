/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 107, 1 November 2026:
Extract the statement of M093.020 from
Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Add the Langlands.NYLL
namespace prefix and place all five source term binders of normClass_ker
inside a closed Prop-valued definition, preserving their order, binder
kinds, shared universe u and subgroup equality.
Import only the published U019 Proofs module. Omit the source proof,
noncomputable section, unused universe v and all other declarations.
The original LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U019.Proofs

/-!
# Kernel of the norm-class homomorphism

The closed proposition identifying the kernel of the canonical norm-class
homomorphism with the actual norm image subgroup.
-/

namespace Langlands.NYLL.LocalFieldTheory

universe u

/-- The kernel of the norm-class homomorphism is the local norm subgroup. -/
def NormClassKerStatement : Prop :=
  ∀ (K L : Type u) [Field K] [Field L] [Algebra K L],
    MonoidHom.ker (normClass K L) = localNormSubgroup K L

end Langlands.NYLL.LocalFieldTheory
