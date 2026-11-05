# Faithful flatness descends from a field extension — theorem interface

Let k be a field, H a commutative k-algebra and K a k-subalgebra. For any field extension k'/k, let K' be the range of k' tensor K → k' tensor H. If k' tensor H is faithfully flat over K', then H is faithfully flat over K. The universes of k, H and k' are independent.

The theorem `Subalgebra.faithfullyFlat_of_faithfullyFlat_range_baseChange` applies the companion `P2MW.S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.md):

The auxiliary `S17Ta.faithfullyFlat_of_faithfullyFlat_baseChange` proves descent for a faithfully flat ring extension R → S. Tensor cancellation and associativity identify the twice extended tensor maps, so injectivity descends. For faithfulness, a proper ideal of R extends to a proper ideal of S, and the assumed faithful module detects that it cannot generate the entire module.

The solution identifies K' with K tensor k' as a K-module, using flatness over the field to prove injectivity. It then constructs inverse maps between K' tensor_K H and k' tensor_k H. These identifications supply both hypotheses of the general descent lemma. The scalar actions and their compatibility are constructed explicitly; no descent assumption is added to the conclusion.

Source: `Theorems/Thm_Subalgebra_faithfullyFlat_of_faithfullyFlat_range_baseChange.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `5b0c841504fa2827308598d1fc9098283b3cc6477277e2a41d165a197e2fc343`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
