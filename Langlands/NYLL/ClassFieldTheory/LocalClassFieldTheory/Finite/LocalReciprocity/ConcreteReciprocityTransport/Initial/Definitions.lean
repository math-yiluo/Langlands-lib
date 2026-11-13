/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)
-/

import Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.IntrinsicAbsoluteData.Initial.Definitions
import Mathlib.FieldTheory.KrullTopology

/-!
# Stable internal names for intrinsic transport data

Adapted by Worker 203 from NYLL commit
`fbd320cd8b1b06487c58227e92eb135794267709`.
See the paired Markdown for the declaration map and complete modification record.
The original license and notices are retained in `licenses/NYLL/LICENSE` and
`licenses/NYLL/NOTICE`.
-/

namespace Langlands.NYLL.PortInternal.M097
open Langlands.NYLL.LocalClassFieldTheory
noncomputable section
variable (K L : Type) [Field K] [Field L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]
abbrev d001 (K : Type) [Field K] :=
  intrinsicAbsoluteGalois K

abbrev d002 (K : Type) [Field K] : Rep ℤ (d001 K) :=
  intrinsicAbsoluteUnits K

abbrev d003 (K : Type) [Field K] : ClosedSubgroup (d001 K) :=
  intrinsicAbstractBase K

noncomputable instance d004 : T2Space (d001 K) :=
  krullTopology_t2
end
end Langlands.NYLL.PortInternal.M097
