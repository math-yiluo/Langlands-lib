/-
Copyright (c) 2026 Naganori Yamaguchi (https://github.com/n-yamaguchi-0729). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Naganori Yamaguchi (assisted by OpenAI Codex)

Modified by Worker 409, 2026-11-14: extract only M335.001 (lines 42–48)
from upstream commit fbd320cd8b1b06487c58227e92eb135794267709; prefix
the namespace with Langlands.NYLL, replace the six source imports by the
published LocalField definitions and canonical CompleteDVF modules, keep
only the opens the extracted unit uses, and replace the module
documentation. See the paired Markdown for the complete record.
The retained license and notices are in licenses/NYLL/.
-/

import Langlands.NYLL.ValuedFieldTheory.LocalField.DiscreteValuationField.Basic.Definitions
import Langlands.NYLL.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.FiniteExtensionCompleteDVF.Canonical

/-!
# The canonical local-field package for Lubin--Tate applications

A topology-first nonarchimedean local field carries the canonical complete
discrete valuation `Langlands.NYLL.LocalFieldTheory.localCompleteDVF`.
This module packages it, with the finiteness of its residue field, as the
shared `LocalField` structure.
-/

noncomputable section

open scoped ValuativeRel

namespace Langlands.NYLL.LubinTate

open LocalFieldTheory.DiscreteValuationField

variable (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

/-- The canonical complete discrete valuation on `K`, together with its
finite residue field, packaged for the standard Lubin--Tate construction. -/
noncomputable def standardLocalField : LocalField K where
  toCompleteDVF := LocalFieldTheory.localCompleteDVF K
  residueFinite := by
    change Finite 𝓀[K]
    infer_instance

end Langlands.NYLL.LubinTate
