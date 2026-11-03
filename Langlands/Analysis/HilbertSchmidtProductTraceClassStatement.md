# Hilbert–Schmidt products are trace class

`Langlands.Analysis.OperatorIdeals.HilbertSchmidtProductTraceClassStatement`
asserts that, for complete complex inner-product spaces E and F, a bounded
Hilbert–Schmidt map B from E to F and a bounded Hilbert–Schmidt map C from
F to E have trace-class composition `C.comp B`. The spaces have independent
arbitrary universes, with no separability or finite-dimension premise.
Swapping the spaces and maps supplies the corresponding conclusion for
`B.comp C`.

The original source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Exercise 9.2 on printed p.267 (one-based PDF
p.279), using Definition 9.1.1 on printed p.240 (PDF p.252).
The original passages were read directly. Registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata was read and does not amend
these passages; `getz-hahn-2024-errata-2026-10` has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source states the result for endomorphisms of a separable Hilbert
space. The rectangular and arbitrary-universe version here is a derived
extension. Both predicates are those of `OperatorIdeals`: Hilbert–Schmidt
membership is witnessed by squared-image summability on one Hilbert
basis, and trace-class membership by summability of the real diagonal
of the positive left modulus sqrt(A A*). Thus the conclusion asserts
trace-class membership of the actual composition, rather than only
summability of its own complex diagonal.

For the internal extension, write A = C B and L = sqrt(A A*).
The identity `‖L x‖ = ‖A* x‖` gives a contractive factorization of L
through A* by extending from its range closure and using orthogonal
projection. Taking adjoints gives L = A U for a bounded U. Then
L = C (B U) is a product of two Hilbert–Schmidt maps, so absolute
complex-diagonal summability for such products implies summability
of the real diagonal of L. This is an intermediate general operator
result, not an automorphic trace-class assertion.

This file defines a proposition. Its proof is a separate obligation;
it supplies no canonical trace, trace-norm inequality, or spectral
decomposition.
