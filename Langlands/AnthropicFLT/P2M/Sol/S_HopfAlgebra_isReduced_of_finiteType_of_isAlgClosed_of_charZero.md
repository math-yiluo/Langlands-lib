# Cartier reducedness over an algebraically closed field

A finite type commutative Hopf algebra A over an algebraically closed characteristic-zero field K is reduced. No reducedness or smoothness premise is assumed.

Reducedness can be checked at all maximal localizations. The finite type Nullstellensatz identifies every maximal ideal J with the kernel of a K-point χ: use the finite integral residue-field extension and algebraic closedness to identify A/J with K. The previous theorem makes the localization at ker χ a domain, hence reduced. Apply the maximal-localization criterion.

Source: `P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `78ecb42cafa39d9cabb3580182d2fbdb5ae0f5e2fbc68fbeb3b3d6b93f728379`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
