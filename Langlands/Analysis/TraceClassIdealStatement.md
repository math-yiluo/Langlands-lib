# Trace-class vector-space, adjoint and ideal laws

`Langlands.Analysis.OperatorIdeals.TraceClassIdealStatement` asserts the
following for complete complex inner-product spaces E and F in independent
arbitrary universes. The existing `IsTraceClass` predicate contains zero
endomorphisms of E and is closed under addition and multiplication by any
complex scalar. An endomorphism is trace class if and only if its Hilbert
adjoint is trace class. If A is trace class on E and B:E→F and C:F→E are
bounded complex-linear maps, then `B.comp A.comp C` is trace class on F.
In particular, taking F=E and one of the bounded maps to be the identity
gives both ordinary endomorphism ideal laws.

This is an internal consequence of the operator infrastructure motivated
by Getz–Hahn, *An Introduction to Automorphic Representations* (2024),
Definition 9.1.1 on printed p.240 (one-based PDF p.252), the basis
discussion on p.241 (PDF p.253), and Exercises 9.1–9.2 on printed p.267
(PDF p.279). These original passages were read directly. The registered
book `getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata was read and does not amend these
passages; `getz-hahn-2024-errata-2026-10` has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.
The book assumes separable Hilbert spaces; the ideal-law collection and
its rectangular, nonseparable scope are internal derived content, not a
claim that these exact quantifiers appear in those passages.

The predicate uses summability of the real diagonal of the positive left
modulus sqrt(A A*) on one actual Hilbert basis. No closure property is
part of its definition. Factor a trace-class map into two Hilbert–Schmidt
maps and use trace-class membership of rectangular Hilbert–Schmidt
products. The scalar, adjoint and bounded-composition laws then follow
from the corresponding Hilbert–Schmidt laws. For addition, combine two
factorizations through the Hilbert direct sum of two copies of E, equipped
with the square-sum norm. The column and row maps are sums of two bounded
compositions with Hilbert–Schmidt maps; their product is the desired sum.

This file defines a proposition and leaves its proof as a separate
obligation. It supplies no trace-norm estimate, completeness of an ideal
norm, trace linearity, or automorphic trace-class existence theorem.
