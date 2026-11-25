/-
Ported from `Definitions/Def_FrobeniusDensity_ClassGroupLSeries.lean` (entire file, 35 lines) of the
Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 3f4f98fc8209bb008d5c0a54a4953a5b20a3b9342711cbcb2af6e9a3a7a9bc6b.
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
import Langlands.MathlibBase

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open Filter Ideal NumberField NumberField.InfinitePlace NumberField.Units Topology
  nonZeroDivisors

open scoped Real

namespace FrobeniusDensity

variable (K : Type u) [Field K] [NumberField K]

noncomputable section

def classZetaCoeff (C : ClassGroup (𝓞 K)) (n : ℕ) : ℕ :=
  Nat.card {I : (Ideal (𝓞 K))⁰ // absNorm (I : Ideal (𝓞 K)) = n ∧ ClassGroup.mk0 I = C}

def classZeta (C : ClassGroup (𝓞 K)) (s : ℂ) : ℂ :=
  LSeries (fun n ↦ classZetaCoeff K C n) s

def classResidue : ℝ :=
  (2 ^ nrRealPlaces K * (2 * π) ^ nrComplexPlaces K * regulator K) /
    (torsionOrder K * Real.sqrt |discr K|)

def classGroupLSeries (χ : ClassGroup (𝓞 K) →* ℂ) (s : ℂ) : ℂ :=
  ∑ C : ClassGroup (𝓞 K), χ C * classZeta K C s

def LSeriesInheritsPole (χ : ClassGroup (𝓞 K) →* ℂ) : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ᶠ s : ℝ in 𝓝[>] 1, c ≤ ‖(fun s : ℝ ↦ (s - 1) * classGroupLSeries K χ s) s‖

end

end FrobeniusDensity
