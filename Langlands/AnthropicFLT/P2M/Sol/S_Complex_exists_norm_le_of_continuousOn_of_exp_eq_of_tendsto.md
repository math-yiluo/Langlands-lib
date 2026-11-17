# Local boundedness of a continuous logarithm with nonzero limit: proof

This module proves `solution`, the statement of `Complex.exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto`. The proof does not use the principal logarithm in place of Λ. Near the nonzero limit c it builds a local logarithm of ℓ. It shows that the difference between Λ and this local logarithm takes values in 2πiℤ and is continuous, so by the intermediate value theorem it is constant near a. The local logarithm is bounded, hence so is Λ.

Source: `P2M/Sol/S_Complex_exists_norm_le_of_continuousOn_of_exp_eq_of_tendsto.lean` (entire file, 161 lines, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `2d494cb7ebf748dc9a98b1dc31aa44cd7080a9e0a3c8f38f721d0d0f6d565471`. Declaration names and namespaces are unchanged.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the proof `Langlands.Global.chebotarevPrimeRealizationStatement` in `Langlands/Global/Arithmetic/ChebotarevPrimeRealizationProof.lean`.

Port changes: imports of FLT modules use the `Langlands.AnthropicFLT` prefix; the source project's finite heartbeat and transparency options (`maxHeartbeats 4000000`, `synthInstance.maxHeartbeats 400000`, `backward.isDefEq.respectTransparency.types false`) are set after the imports; the audit's modification comments are replaced by the port header; the import of `P2M.Util` is dropped. The mathematical hypotheses and conclusions of the source are retained.

None of the audited compatibility, universe or cleanup edits touches this module.
