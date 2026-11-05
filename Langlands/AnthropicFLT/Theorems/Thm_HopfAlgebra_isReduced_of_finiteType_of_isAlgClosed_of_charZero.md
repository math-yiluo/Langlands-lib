# Cartier reducedness over an algebraically closed field — theorem interface

A finite type commutative Hopf algebra A over an algebraically closed characteristic-zero field K is reduced. No reducedness or smoothness premise is assumed.

The theorem `HopfAlgebra.isReduced_of_finiteType_of_isAlgClosed_of_charZero` applies the companion `P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.md):

Reducedness can be checked at all maximal localizations. The finite type Nullstellensatz identifies every maximal ideal J with the kernel of a K-point χ: use the finite integral residue-field extension and algebraic closedness to identify A/J with K. The previous theorem makes the localization at ker χ a domain, hence reduced. Apply the maximal-localization criterion.

Source: `Theorems/Thm_HopfAlgebra_isReduced_of_finiteType_of_isAlgClosed_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `610e33c922aaf4884561de6c9f434da04ae810b27651493d5441ae073b26a059`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
