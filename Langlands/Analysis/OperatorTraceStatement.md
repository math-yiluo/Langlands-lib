# Operator trace: basis formula, linearity and bounded cyclicity

Worker 116 states the laws needed to interpret the actual chosen-basis formula
`operatorTrace` as the trace on actual trace-class endomorphisms. All four
statements are proposition definitions; this module supplies no proofs.

`OperatorTraceBasisStatement` quantifies over a complete complex inner-product
space E, a bounded endomorphism A, and an arbitrary Hilbert basis b, whose index
has an independent universe. If A is trace class, its complex diagonal in b
is absolutely summable and `operatorTrace A = traceIn b A`. Thus the
identification includes a convergence assertion, rather than merely equality
of total `tsum` values. Its intended proof compares b with the fixed basis
chosen in `operatorTrace`, using `TraceBasisIndependenceStatement`.

`OperatorTraceLinearityStatement` asserts the zero formula and, for trace-class
A and D, additivity of the trace; it also asserts
`operatorTrace (c • A) = c * operatorTrace A` for every complex c and trace-class
A. The trace-class ideal-law target separately guarantees that the sum and
scalar multiple are trace class. No linearity on all bounded endomorphisms is
claimed. Absolute convergence and termwise linearity justify the intended
sum manipulations on this domain.

`OperatorTraceCyclicityStatement` uses two complete complex inner-product
spaces in independent arbitrary universes. For trace-class A:E→E and arbitrary
bounded complex-linear B:E→F and C:F→E it asserts that both `(B A) C` on F and
`A (C B)` on E are trace class, and that their operator traces agree. The first
expression is explicitly `(B.comp A).comp C`; the second is
`A.comp (C.comp B)`. Taking F=E and C to be the identity gives ordinary bounded
cyclicity `tr(B A) = tr(A B)`. Neither B nor C is required to be trace class,
Hilbert–Schmidt, invertible or an isometry. A Hilbert–Schmidt factorization of
A, ideal laws and two product-diagonal comparisons supply the intended route.

`OperatorTraceLawsStatement.{u,v,w}` is exactly the conjunction of the basis
statement for space universe u and basis universe w, linearity for u, and
cyclicity for space universes u and v. No universe equality, separability or
finite-dimensionality hypothesis is imposed.

The source motivation is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), trace definition on printed p.240, basis independence
on p.241, and Exercises 9.1–9.2 on p.267 (one-based PDF pp.252–253 and 279),
registered as `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata, registered as
`getz-hahn-2024-errata-2026-10`, SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`,
was read and does not amend these passages. Mathlib's inner product is linear
in its second argument, and the unchanged trace-class predicate uses the
positive left modulus `sqrt(A A*)`.

The law collection is internal derived content. The source works on separable
Hilbert spaces; arbitrary independent universe levels, rectangular bounded
sandwiches and this exact conjunction are not attributed to a printed theorem.
The intended arguments use the existing actual operator predicates and
factorization, basis-independence, product and ideal results. Existence of
trace-class automorphic convolution operators, trace-norm estimates and any
spectral or kernel formula remain separate obligations.
