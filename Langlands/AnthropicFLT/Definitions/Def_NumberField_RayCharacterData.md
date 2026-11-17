# Parity, primitivity and Gauss sums of narrow ray class characters

Let K be a number field, 𝔣 an ideal, χ a character of the narrow ray class group modulo 𝔣 and S a set of real places. The module defines the following.
- `signAt K S x`: the product of the signs of x at the places in S.
- `chiIdeal K 𝔣 χ I`: χ extended to fractional ideals, equal to 0 on ideals that are zero or not coprime to 𝔣.
- `IsParity K 𝔣 χ S`: for nonzero α ≡ 1 modulo 𝔣, χ((α)) equals the sign of α at S.
- `chiFin`: the finite part of χ.
- `IsPrimitiveMod`: for every strictly larger ideal 𝔣′, some totally positive α ≡ 1 modulo 𝔣′ has χ((α)) different from 0 and 1.
- `addChar x = exp(2πi·Tr_{K/ℚ}(x))`, the Gauss sum `gaussSumAt` at a point y, and the Gauss datum predicate `IsGaussDatum`.

It proves that the trivial character has the empty parity set and that every character modulo (1) is primitive.

Source: `Definitions/Def_NumberField_RayCharacterData.lean` (entire file, 85 lines) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `a9b53b953b3e2219bb3fbdf1331a7a23252324affa0b805e5688381e051717b9`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header. Apart from the universe generalization, the mathematical hypotheses and conclusions of the source are retained.

The following edits of the audit `notes/reuse/anthropic-chebotarev-audit.md` are applied. Its evidence files `compatibility.md`, `universes.md` and `cleaned.md` in `notes/reuse/anthropic-chebotarev-evidence/` give the exact diffs.

- Universes: `universe u v w` is declared; the binder of `K` (originally `Type`) is `Type u`. The audit named these universes `audit_u`, `audit_v`, `audit_w`.
