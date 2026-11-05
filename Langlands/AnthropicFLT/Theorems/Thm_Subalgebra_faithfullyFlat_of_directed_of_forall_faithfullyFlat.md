# Faithful flatness over a directed union of subalgebras — theorem interface

For a nonempty directed family F of k-subalgebras of H contained in K and covering every element of K, faithful flatness of H over every F(i) implies faithful flatness over K. The family index has its own universe. Neither K nor the family members are assumed finitely generated.

The theorem `Subalgebra.faithfullyFlat_of_directed_of_forall_faithfullyFlat` applies the companion `P2MW.S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.md):

Directedness first puts every finite collection of coefficients into one F(i). Flatness is checked on finitely generated ideals of K: express a tensor by finitely many generators, transfer the resulting relation to the ideal they generate over F(i), use flatness there, and map the vanishing tensor back by a balanced additive map. For faithfulness, a finite expression for 1 in an extended ideal is transferred to F(i). Faithfulness over F(i) makes that smaller ideal the unit ideal; its expression for 1 maps back into the original ideal of K.

Source: `Theorems/Thm_Subalgebra_faithfullyFlat_of_directed_of_forall_faithfullyFlat.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `5852299dcfcae88fe99faa0041f277fb7900bc08f2cfb5b8109f6460963e27d7`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
