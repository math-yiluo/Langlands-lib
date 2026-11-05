# The antipode of a commutative Hopf algebra is involutive

For a Hopf algebra A over a commutative semiring R, with A itself commutative, the antipode satisfies S(S(a)) = a. Cocommutativity of the coalgebra is not assumed.

The proof works in the convolution monoid of R-linear endomorphisms. The Hopf identities show S * id = 1. Applying S to the corresponding finite comultiplication sum and using commutativity shows (S composed with S) * S = 1. Uniqueness of a left and a right inverse gives S composed with S = id, and evaluation gives the elementwise conclusion.

Source: `P2M/Sol/S_HopfAlgebra_antipode_antipode.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `f57782c6801bf2e477a7060c07da4742ce9568156d4fef5c751423d970e6e695`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
