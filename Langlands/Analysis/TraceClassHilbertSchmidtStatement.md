# Trace-class operators are Hilbert–Schmidt

`Langlands.Analysis.OperatorIdeals.TraceClassHilbertSchmidtStatement`
asserts that every trace-class bounded complex-linear endomorphism of a
complete complex inner-product space is Hilbert–Schmidt. The space has an
arbitrary universe and need not be separable or finite dimensional.

Both predicates are the existing definitions from `OperatorIdeals`.
`IsTraceClass A` means that in some actual Hilbert basis the real diagonal
of the positive **left** modulus `L = CFC.sqrt (A * star A)` is summable.
`IsHilbertSchmidt A` means that the squared image norms are summable in
some actual Hilbert basis. These are genuine summability premises and
conclusions; neither predicate supplies a basis-independence theorem.
The modulus is the square root of `A A*`, following the source convention,
and the inner product is linear in its second argument.

Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Definition 9.1.1 and (9.3), printed p. 240 (one-based PDF p. 252), give
the operator predicates. Exercise 9.3, printed p. 267 (PDF p. 279),
asks for this implication, and Corollary 9.3.2, printed p. 247
(PDF p. 259), uses it. These passages were read directly.
The registered source is `getz-hahn-2024-automorphic-representations`,
SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete five-page October 2026 author errata was read and does not
amend these operator assertions. Its registration is
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separable Hilbert spaces. The arbitrary-index version
here is a derived extension of the same implication. Put `B = sqrt L`.
Positivity gives self-adjointness, `L² = A A*` and `B² = L`. Hence
`‖A* x‖² = ‖L x‖² ≤ ‖B‖² ‖B x‖²
= ‖B‖² Re⟪x, L x⟫`. Summability of the modulus diagonal therefore
gives square summability of `A*` on the witnessing basis. Parseval,
the adjoint identity and exchange of nonnegative double sums transfer
that summability back to `A` on the same basis. None of these steps
requires a countable enumeration or a separability hypothesis.

This module defines the target proposition. Its proof is a separate
exact-target obligation after publication. Canonical trace and trace norm,
trace-class ideal laws, trace-class products of Hilbert–Schmidt operators,
compactness, and automorphic convolution remain separate obligations.
