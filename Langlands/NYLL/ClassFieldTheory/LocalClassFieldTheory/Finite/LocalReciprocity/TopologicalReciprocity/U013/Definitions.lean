/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 11 November 2026: extract M257.013 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Prefix the namespace with
Langlands.NYLL, use focused published imports, and restore the source-local
quotient topology locally. Keep the source Type-zero boundary and all
elaborated parameters; unused section hypotheses are omitted.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TopologicalReciprocity.U001.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U005.Definitions

/-! # The continuous norm-class projection -/

noncomputable section

namespace Langlands.NYLL.LocalClassFieldTheory

open Langlands.NYLL.LocalFieldTheory

attribute [local instance] Langlands.NYLL.PortInternal.M257.d001

variable (K L : Type) [Field K] [Field L] [Algebra K L] [TopologicalSpace K]

/-- The quotient map to the norm quotient, bundled as a continuous
homomorphism for the native quotient topology. -/
noncomputable def normClassContinuous :
    Kˣ →ₜ* NormQuotient K L :=
  { normClass K L with
    continuous_toFun := QuotientGroup.continuous_mk }

end Langlands.NYLL.LocalClassFieldTheory
