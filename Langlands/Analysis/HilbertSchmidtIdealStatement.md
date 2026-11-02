# Hilbert–Schmidt vector-space and ideal laws

`Langlands.Analysis.OperatorIdeals.HilbertSchmidtIdealStatement` states six
properties of the existing `IsHilbertSchmidt` predicate on actual continuous
complex-linear maps. For complete complex inner-product spaces `E`, `F`
and `G` in three independent universes, it asserts:

- The zero map from `E` to `F` is Hilbert–Schmidt.
- The sum of two Hilbert–Schmidt maps from `E` to `F` is Hilbert–Schmidt.
- Every complex scalar multiple of a Hilbert–Schmidt map is Hilbert–Schmidt.
- A map from `E` to `F` is Hilbert–Schmidt if and only if its Hilbert
  adjoint from `F` to `E` is Hilbert–Schmidt.
- Postcomposition with any bounded complex-linear map from `F` to `G`
  preserves the predicate.
- Precomposition with any bounded complex-linear map from `G` to `E`
  preserves the predicate.

The spaces need not be separable or finite dimensional. Each basis in the
existing predicate is an actual Hilbert basis with an arbitrary index set,
and the maps need not be endomorphisms. Composition is ordinary composition
of bounded linear maps, with the displayed domains and codomains; no
unitarity, injectivity or invertibility is required.

This is a derived operator-theoretic interface for the general automorphic
program. Its source definition is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and equation (9.3), printed p. 240
(one-based PDF p. 252), registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The source works with separable endomorphisms. It does not state the present
six-part rectangular, arbitrary-index conjunction at that passage.
The complete five-page October 2026 errata was also read; its Chapter 9
entries do not amend that definition. It is registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The derivation uses Parseval and the adjoint identity to equate the
nonnegative extended sums of squared images on domain and codomain Hilbert
bases. Interchanging nonnegative double sums needs no countability
assumption. Finiteness gives adjoint invariance and transfers summability
between domain bases. On a common basis the inequality
`‖x + y‖² ≤ 2 * (‖x‖² + ‖y‖²)` gives closure under addition, and the
scalar norm identity gives closure under scalar multiplication.
The bound `‖B (A x)‖² ≤ ‖B‖² * ‖A x‖²` gives postcomposition;
adjoint invariance and reversal of composition give precomposition.
Zero follows from existence of a Hilbert basis and summability of zero.

This module defines a proposition and supplies no proof. It makes no
canonical-norm, trace-class, compactness, convolution or spectral
decomposition claim. Its proof is a separate exact-target obligation.
