# A Jacobson spectrum criterion for an open set to be the whole space

For a Jacobson commutative ring A, a nonempty open subset U of Spec A is the whole space if membership of a maximal prime implies membership of every maximal prime. The hypothesis is a transitivity condition on closed points, not on arbitrary primes.

Write the closed complement as a zero locus. A point of U supplies an element outside its prime and hence outside the nilradical. The Jacobson property supplies a maximal ideal not containing that element, giving a maximal point in U. If any prime were outside U, a maximal ideal above it would also lie in the closed complement. Transitivity puts that maximal point in U, a contradiction.

Source: `P2M/Sol/S_PrimeSpectrum_eq_univ_of_isOpen_of_nonempty_of_forall_isMaximal.lean` (entire file, including its solution and auxiliary declarations) in the registered source `anthropic-flt-complete-lean-source-6e837e75`, commit `6e837e75355538c7f80bab5b956861e86c4eacc2`. Original file SHA256: `b6be0b5fa8908eb9f4ccfaedf8d60aa46b418ded8c3f90b6ebe07f1ab1fa29d2`.

Copyright 2026 Anthropic, PBC; Apache License 2.0. The retained license, notice and attribution ledger are in `licenses/Anthropic-FLT/`. The source attribution ledger has no entry for this file. This module is supporting mathematics imported for the actual affine homomorphism image proof.

Port changes: imports use the `Langlands.AnthropicFLT` prefix; the utility import and P2M namespace commands are replaced by ordinary Lean commands. The finite heartbeat and transparency settings reproduce the source project configuration. The mathematical hypotheses and conclusions are retained.
