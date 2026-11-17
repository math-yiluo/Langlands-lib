# Partial zeta functions of ideal classes

For a number field K and an ideal class C, `classZetaCoeff K C n` is the number of nonzero integral ideals of norm n in C, and `classZeta K C` is the associated Dirichlet series. `classResidue K = 2^(r₁)·(2π)^(r₂)·R_K / (w_K·√|d_K|)` is the class-number-formula residue. For a character χ of the class group, `classGroupLSeries K χ s = Σ_C χ(C)·classZeta(C, s)`. The Prop-valued definition `LSeriesInheritsPole K χ` says that |(s − 1)·L(s, χ)| is bounded below by a positive constant as s → 1⁺. This is a definition only: the port neither proves nor assumes it.

Source: `Definitions/Def_FrobeniusDensity_ClassGroupLSeries.lean` (entire file, 35 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `3f4f98fc8209bb008d5c0a54a4953a5b20a3b9342711cbcb2af6e9a3a7a9bc6b`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type*`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
