# Compactness of Hilbert–Schmidt operators

`Langlands.Analysis.OperatorIdeals.HilbertSchmidtCompactStatement` asserts
that every Hilbert–Schmidt continuous complex-linear map between two complex
Hilbert spaces is compact. The domain and codomain have independent arbitrary
universes. Neither space is required to be separable or finite dimensional,
and the map need not be an endomorphism.

The premise is the existing `IsHilbertSchmidt A`: there exist a subset of the
domain and an actual Hilbert basis indexed by that subset for which the real
family of squared image norms is summable. The conclusion is Mathlib's
`IsCompactOperator A`. For these normed spaces, this is equivalent to
compactness of the closure of the image of the unit ball. It does not mean
that the operator's entire range is a compact set.

The original source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and (9.3), printed p. 240
(one-based PDF p. 252), Exercise 9.3, printed p. 267 (PDF p. 279), and its
use in Corollary 9.3.2, printed p. 247 (PDF p. 259). The registered source
is `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
These passages were read directly. The complete five-page October 2026
author errata was also read; it does not amend these operator assertions.
Its registration is `getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separable Hilbert spaces and discusses endomorphisms.
The present target is a derived rectangular, arbitrary-index extension.
A finite-rank approximation argument supplies its intended route: truncate
the expansion in the witnessing Hilbert basis; Cauchy–Schwarz and Bessel's
inequality bound the operator-norm error by the square root of the omitted
squared-image sum. Summability makes this bound tend to zero. Each finite
sum is compact, and compact operators are closed for the operator norm.
This route needs only the witnessing basis, without first proving basis
independence or countability of a basis of the ambient space.

This module states the proposition; it does not prove it. The proof belongs
in a separate exact-target proof task after this statement is published.
Trace class implying Hilbert–Schmidt, trace-class composition, operator
ideal laws, construction of compact convolution operators, and cuspidal
spectral decomposition remain separate obligations.
