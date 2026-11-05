# Translation carries a rational point to the augmentation point — theorem interface

For any commutative Hopf algebra A over a field K and any K-point χ: A → K, there is a K-algebra automorphism e whose inverse image of the augmentation ideal is ker χ. No finite type or characteristic restriction is needed.

The theorem `HopfAlgebra.exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom` applies the companion `P2MW.S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.md):

Right translation by χ is obtained by applying χ to the second factor of comultiplication. Right translation by χ composed with the antipode is its inverse. Both inverse identities are proved from coassociativity and the two Hopf antipode identities using finite comultiplication representations. The counit composed with right translation equals χ; taking kernels proves the stated ideal identity.

Source: `Theorems/Thm_HopfAlgebra_exists_algEquiv_comap_ker_counitAlgHom_eq_ker_algHom.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `c2160d67efb6b90c25f417aae2b64a371802ace47d210fbf312e1c2c30f9f06f`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
