# Partial and completed L-series of narrow ray class characters

For a number field K, an ideal 𝔣 and a class C of the narrow ray class group modulo 𝔣, `rayZetaCoeff K 𝔣 C n` is the number of nonzero integral ideals of norm n that are coprime to 𝔣 and lie in C. `rayZeta` is the associated Dirichlet series. For a character χ, `rayClassLSeries K 𝔣 χ s = Σ_C χ(C)·rayZeta(C, s)`. For a set S of real places, the completed L-function is

completedRayL K 𝔣 χ S s = (|d_K|·N(𝔣))^(s/2) · Γ_ℝ(s)^(r₁ − |S|) · Γ_ℝ(s + 1)^|S| · Γ_ℂ(s)^(r₂) · L(s, χ),

with r₁ real and r₂ complex places.

Source: `Definitions/Def_NumberField_CompletedRayL.lean` (entire file, 34 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `77de528a686fea526ce3873c96914f496aca00f1cbfcdc58398290f70184b1b0`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
