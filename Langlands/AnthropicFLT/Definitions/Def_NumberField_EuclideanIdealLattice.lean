/-
Ported from `Definitions/Def_NumberField_EuclideanIdealLattice.lean` (entire file, 34 lines) of the
Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 019fb7c4fdc7a9161234fe45d44229656b0840dac1b0a0ee9b6a95350e004957.
Copyright 2026 Anthropic, PBC, licensed under the Apache License, Version 2.0; see
`licenses/Anthropic-FLT/LICENSE`, `NOTICE` and `ATTRIBUTION.md`.

Complete list of edits to the source text (the paired Markdown file gives the same list; the audit
`notes/reuse/anthropic-chebotarev-audit.md` and its evidence files `compatibility.md`,
`universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact
diffs):
- Imports of FLT modules use the `Langlands.AnthropicFLT` prefix.
- The source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`,
  `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set
  after the imports.
- The audit's modification comments are replaced by the port header.
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The
  audit named these universes `audit_u`, `audit_v`, `audit_w`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Mathlib.NumberTheory.NumberField.CanonicalEmbedding.Basic
import Mathlib.NumberTheory.NumberField.Discriminant.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open NumberField NumberField.mixedEmbedding
open scoped nonZeroDivisors

noncomputable section

namespace Deep.Analytic

variable (K : Type u) [Field K] [NumberField K]

open Classical in

def euclideanIdealLattice (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) :
    Submodule ℤ (euclidean.mixedSpace K) :=
  ZLattice.comap ℝ (mixedEmbedding.idealLattice K I) (euclidean.toMixed K).toLinearMap

end Deep.Analytic

namespace M4aP2

variable (K : Type u) [Field K] [NumberField K]

def heckeScale (I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : ℝ :=
  (|(discr K : ℝ)| * (FractionalIdeal.absNorm (I : FractionalIdeal (𝓞 K)⁰ K) : ℝ) ^ 2)
    ^ (-(1 : ℝ) / (Module.finrank ℚ K : ℝ))

end M4aP2

end
