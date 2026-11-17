/-
Ported from `Definitions/Def_FrobeniusDensity_DegOneAsymptotic.lean` (entire file, 44 lines) of the
Anthropic Lean formalization of Fermat's Last Theorem: registered source
`anthropic-flt-complete-lean-source-6e837e75`, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
original file SHA256 3fa91cc61916676dd0c95fc1a691282e1437d24b71ca03b2bdd4e28c78ab3ef7.
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
- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`; the
  binder of `L` (originally `Type*`) is `Type v`. The audit named these universes `audit_u`,
  `audit_v`, `audit_w`.

Declaration names and namespaces are unchanged. Apart from the universe generalization, the
mathematical hypotheses and conclusions of the source are retained.
-/
import Langlands.AnthropicFLT.Definitions.Def_TaylorWiles_Primes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.FieldTheory.Fixed

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

universe u v w

set_option autoImplicit false

open scoped NNReal
open Filter Topology Asymptotics

namespace FrobeniusDensity

open NumberField Ideal

section DegOneCount

variable (K : Type u) [Field K] [NumberField K]

open scoped Classical in

noncomputable def degOneCount (ℓ : ℕ) : ℕ :=
  if ℓ.Prime then
    {𝔮 ∈ (ratPrimeIdeal ℓ).primesOver (𝓞 K) | Nat.card ((𝓞 K) ⧸ 𝔮) = ℓ}.ncard
  else 0

end DegOneCount

section AnalyticInput

variable (L : Type v) [Field L] [NumberField L] [IsGalois ℚ L]

def DegOneAsymptotic : Prop :=
  ∀ (H : Subgroup (L ≃ₐ[ℚ] L)) (S₀ : Finset ℕ),
    (∀ s : ℝ, 1 < s → Summable (fun ℓ : ℕ => (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s))) ∧
    (fun s : ℝ => (∑' ℓ : ℕ, (if ℓ ∈ S₀ then 0 else
        (degOneCount (FixedPoints.intermediateField H : IntermediateField ℚ L) ℓ : ℝ))
      * (ℓ : ℝ) ^ (-s)) + Real.log (s - 1)) =O[𝓝[>] 1] (fun _ => (1 : ℝ))

end AnalyticInput

end FrobeniusDensity
