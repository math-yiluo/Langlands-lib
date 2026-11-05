# Cartier reducedness over an arbitrary characteristic-zero field

A finite type commutative Hopf algebra A over any characteristic-zero field K is reduced. The field need not be algebraically closed.

Extend scalars to the algebraic closure Ω of K. The tensor product Ω tensor_K A remains a finite type commutative Hopf algebra and is reduced by the algebraically closed theorem. The natural map A → Ω tensor_K A is injective, by flatness over a field and injectivity of K → Ω. Reducedness descends along this injective ring map.

Source: `P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `4de8f426fcf0f68e84b67b7ec1927cf5f453773620c0aa0468b3128be9665269`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
