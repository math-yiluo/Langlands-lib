# Trace-class basis characterization and trace-norm independence

`Langlands.Analysis.OperatorIdeals.TraceNormBasisIndependenceStatement`
asserts three facts for every complete complex inner-product space E,
bounded complex-linear endomorphism A and two actual Hilbert bases b and c.
The space and the two basis index types have independent arbitrary
universes.

First, `IsTraceClass A` is equivalent to real summability of
`Re⟪b i, leftModulus A (b i)⟫` in the specified basis b. The existing
predicate uses an existential basis indexed by a subset of E; the
assertion transfers it to any given basis. Second, the real diagonal
families in b and c are summable together. Third, when the family in b
is summable, the existing sums `traceNormIn b A` and `traceNormIn c A`
are equal. No nonsummable total `tsum` is interpreted as a trace norm.

The modulus is the existing positive **left** modulus
`L = CFC.sqrt (A * star A)`, so multiplication means composition and
`star A` is the Hilbert adjoint. The real part follows Mathlib's
second-argument-linear complex inner product. This is the same diagonal
and modulus convention as the existing `OperatorIdeals` definitions.
Neither separability nor finite-dimensionality is assumed.

The original source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and equation (9.3), printed
p.240 (one-based PDF p.252), the independence assertion on p.241
(PDF p.253), and Exercise 9.1 on p.267 (PDF p.279). These passages were
read directly. The source is registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete five-page October 2026 author errata was read and does not
amend these passages. It is registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separable Hilbert spaces and states trace-norm
independence for trace-class operators. The arbitrary-index version and
explicit existential-basis characterization here are derived extensions.
For `B = CFC.sqrt L`, positivity and the square-root identity give
`B* = B`, `B² = L` and
`Re⟪x, L x⟫ = ‖B x‖²`. Thus the summability and equality questions
reduce to Hilbert–Schmidt squared-image basis independence for the
actual bounded operator B. The published theorem
`hilbertSchmidtBasisIndependence` supplies that result with arbitrary
indices. Comparing any supplied basis with a subset-indexed Hilbert
basis gives the characterization of `IsTraceClass`.

This file defines the proposition target. Its proof is a separate
exact-target obligation after publication. It does not construct a
canonical trace norm or prove its norm axioms, absolute summability or
basis independence of the complex trace diagonal, trace-class ideal
laws, or any automorphic trace-class assertion.
