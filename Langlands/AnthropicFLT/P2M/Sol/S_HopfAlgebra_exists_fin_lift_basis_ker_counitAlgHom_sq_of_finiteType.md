# A finite lifted basis of the augmentation cotangent space

For a finite type commutative Hopf algebra A over a field K, choose n and ξ: Fin n → A lying in the augmentation ideal I, linearly independent modulo I², and spanning every element of I modulo I² over K. Characteristic zero is not needed.

Noetherianity gives finitely many ideal generators of I. Modulo I², every coefficient multiplying a generator can be replaced by its counit scalar: the coefficient minus that scalar lies in I. Thus the images of those generators span a finite dimensional K-subspace of A/I² containing the image of I. Choose a basis of this space, lift each vector back to I, and reindex it by Fin n. The basis identities give linear independence and the required spanning congruence.

Source: `P2M/Sol/S_HopfAlgebra_exists_fin_lift_basis_ker_counitAlgHom_sq_of_finiteType.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `7dd9e64dc8afcc65a2d66e8a2bf2ed2bd2334de8ea80ac2a1978b1c9e90c0825`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
