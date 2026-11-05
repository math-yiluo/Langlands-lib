# Cartier reducedness over an arbitrary characteristic-zero field — theorem interface

A finite type commutative Hopf algebra A over any characteristic-zero field K is reduced. The field need not be algebraically closed.

The theorem `HopfAlgebra.isReduced_of_finiteType_of_charZero` applies the companion `P2MW.S_HopfAlgebra_isReduced_of_finiteType_of_charZero.solution` with the displayed arguments. Its proof is implemented in [the solution module](../P2M/Sol/S_HopfAlgebra_isReduced_of_finiteType_of_charZero.md):

Extend scalars to the algebraic closure Ω of K. The tensor product Ω tensor_K A remains a finite type commutative Hopf algebra and is reduced by the algebraically closed theorem. The natural map A → Ω tensor_K A is injective, by flatness over a field and injectivity of K → Ω. Reducedness descends along this injective ring map.

Source: `Theorems/Thm_HopfAlgebra_isReduced_of_finiteType_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `74251bc31f3007211b615e3a93c2dd3dbb2228f9992b727e7f7f777cf9d36704`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. The source wrapper tactic is replaced by an explicit application of its companion solution.
