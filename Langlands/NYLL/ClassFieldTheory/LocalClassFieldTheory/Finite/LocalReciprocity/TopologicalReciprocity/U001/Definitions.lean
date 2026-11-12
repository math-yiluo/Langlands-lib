/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

/-
Modifications by Worker 120, 10 November 2026: extract M257.001 from
Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TopologicalReciprocity.lean
at fbd320cd8b1b06487c58227e92eb135794267709. Give the source-local
instance a stable PortInternal name, retain local scope and the Type-zero
parameters, and use the published norm quotient and focused Mathlib imports.
LICENSE and NOTICE are retained in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient.U002.Definitions
import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.Topology.Algebra.Group.Units

/-! # The local topology instance on the norm quotient -/

namespace Langlands.NYLL.PortInternal.M257

open Langlands.NYLL.LocalFieldTheory

noncomputable local instance d001
    (K L : Type) [Field K] [Field L] [Algebra K L]
    [TopologicalSpace K] :
    TopologicalSpace (NormQuotient K L) := by
  change TopologicalSpace (Kˣ ⧸ localNormSubgroup K L)
  infer_instance

end Langlands.NYLL.PortInternal.M257
