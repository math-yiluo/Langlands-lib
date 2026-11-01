# Complementary anti-triangular Fourier slices

Worker 1198. This is an internal specialization of the published
`rectangularCoordinateSlice_fourier_duality` for the JPSS Section 6.2 rectangular
identity. It does not assert the actual unipotent identity or identify Haar
normalizations.

The duality theorem assumes a Hausdorff locally compact totally disconnected
field `K`, continuous ring operations, and its Borel measurable structure.
It uses a supplied continuous nontrivial unitary additive character `ψ` and
a supplied sigma-finite regular additive Haar measure `ν` satisfying
`IsSelfDual ψ ν`. This scalar Fourier normalization is an essential
hypothesis, separate from any comparison with the group Haar. For every
natural `n`, including zero, the input `Φ` is a Schwartz–Bruhat function on
`(n+1)`-square matrices. Its Fourier transform is the plus-character
`rectangularFourierIntegral ψ ν`, using the nested finite product of that
same `ν` on all matrix entries.

In square size `n + 1`, the right slice has free entries `n < i + j` and fixed
antidiagonal entries one. The complementary left slice has free entries
`i + j ≤ n` and fixed entries minus one on `i + j = n + 1`. All other fixed
entries are zero. Their measures are exactly the nested supplied-scalar-Haar
and Dirac coordinate measures, including size one.

The two masks are evaluated entrywise. Pairing with the right fixed
antidiagonal is the sum `X i i.rev`; pairing with the negative of the left
fixed shifted antidiagonal is the sum `Y i.succ i.rev.succ`. Substitution in
the published complementary-slice theorem proves both integrability claims
and the equality, with those positive displayed phases. No matrix transpose,
representation, or unipotent measure comparison is used in this module.
