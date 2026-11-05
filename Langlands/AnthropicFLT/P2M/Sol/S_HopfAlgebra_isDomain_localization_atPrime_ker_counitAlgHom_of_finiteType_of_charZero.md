# The local ring at the identity is a domain in characteristic zero

For a finite type commutative Hopf algebra A over a characteristic-zero field K, the localization of A at the kernel I of the counit is an integral domain. The kernel is prime since the counit takes values in the field.

Choose the finite lifted basis of I/I² and use the augmentation-order multiplication theorem. It first proves saturation of every I-power under multiplication by an element outside I. Krull intersection in the Noetherian local ring shows that the numerator of a nonzero localized element has finite I-adic order. If two nonzero fractions had zero product, clearing denominators and saturation would put the product of their numerators into every I-power. Their finite exact orders and the multiplication theorem contradict this. Nontriviality of the prime localization completes the domain structure.

Source: `P2M/Sol/S_HopfAlgebra_isDomain_localization_atPrime_ker_counitAlgHom_of_finiteType_of_charZero.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `1c56dbe60be4ee4bdc258da4610b8721d9908bba0324741d701ce5cf8e340d2f`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
