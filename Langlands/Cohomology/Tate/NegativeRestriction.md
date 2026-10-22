# The norm-kernel formula for restriction

Authors: Worker 45 and Worker 210. Worker 45 wrote the Lean proof; Worker 210
audited it and prepared the accompanying documentation.

This module proves the actual degree-minus-one formula for
subgroup restriction. For the chosen representatives `q.out` of the left
cosets, it sends the class of a full-norm-zero vector `a` to the class of
`inverseCosetSum H A a` (from `InverseCosetSum`), the sum of `q.out⁻¹ • a`
over all cosets. The subgroup norm of this sum is
the full norm of `a`, by the explicit coset factorization already proved
in `ZeroTransferDefinitions`.

The proof uses the actual coinduced augmentation sequence. An invariant
lift of the full norm computes its connecting image. Applying the
inverse-coset sum to the original lift computes the subgroup connecting
image. Degree-zero restriction, the proved connecting-map compatibility,
and the injective actual shift isomorphism give the asserted identity.
The formula is not assumed as part of the operation's data.

Source: Serre, *Local Fields*, Springer GTM 67 (1979), Chapter VII, section 7,
printed pages 118–119 (PDF pages 124–125), and Chapter VIII, section 1, printed
pages 127–129 (PDF pages 133–135). The precise inverse convention follows
Mathlib's right-module convention for ordinary homological chains.
