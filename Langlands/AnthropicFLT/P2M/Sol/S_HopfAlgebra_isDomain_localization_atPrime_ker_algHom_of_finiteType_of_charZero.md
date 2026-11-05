# The local ring at every rational point is a domain

For a finite type commutative Hopf algebra A over a characteristic-zero field K and a K-point χ, the localization at ker χ is a domain.

Choose the translation automorphism whose inverse image of the augmentation ideal is ker χ. It sends the complement of ker χ onto the complement of the augmentation ideal, so it induces a ring isomorphism of the two prime localizations. Transport the domain structure from the localization at the counit kernel through this isomorphism.

Source: `P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_algHom_of_finiteType_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `f03220db2c4492966a1f3b69552e910bfb26e28540751ef79135eed1d0bfb46b`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
