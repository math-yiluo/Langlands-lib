# The Hopf algebra quotient by a stable ideal

For a commutative Hopf algebra A over a field F and an ideal I killed by the counit, preserved by the antipode, and killed by quotienting both factors of comultiplication, there is a quotient Hopf algebra A' and a surjective bialgebra map π with kernel I. The result also preserves cocommutativity and finite dimension when present, and gives the ordinary algebra quotient universal property for test algebras in the stated universe.

The chosen A' is A/I. Ideal quotient lifts define its comultiplication, counit and antipode. Surjectivity of the quotient map reduces the counit, coassociativity and antipode laws to the corresponding identities on A; tensor naturality handles the comultiplication identities. The usual quotient construction proves the kernel formula and unique factorization property. Surjective linear image gives finite dimension, and the tensor flip identity gives cocommutativity.

Source: `P2M/Sol/S_HopfAlgebra_exists_hopfAlgebra_bialgHom_surjective_ker_eq_of_hopfIdeal.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `65d72291b719eebc5890f868611410b1921d54f8e1af356a849af84fac8a88f3`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained. Tensor inductions explicitly select the three-case recursor where the current default eliminator has changed.
