# Absolute summability and basis independence of the complex trace

`Langlands.Analysis.OperatorIdeals.TraceBasisIndependenceStatement`
concerns an actual bounded complex-linear endomorphism A of a complete
complex inner-product space, satisfying the existing existential-basis
`IsTraceClass` predicate. For any two supplied Hilbert bases b and c,
it asserts absolute summability of both complex diagonal families
and equality of `traceIn b A` and `traceIn c A`. The space and the two
basis index types have three independent arbitrary universes.

The original source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and the trace definition on
printed p.240 (one-based PDF p.252), the trace basis-independence
assertion on p.241 (PDF p.253), and Exercise 9.1 on p.267
(PDF p.279). Those original passages were read directly. Registered
source `getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata was read and does not amend
these passages; `getz-hahn-2024-errata-2026-10` has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separability and uses a sequence of basis vectors.
This target extends that basis-index scope and explicitly records
absolute summability, so that Mathlib's total `tsum` is used only
with the required convergence guarantee. Mathlib's complex inner
product is linear in its second argument; the diagonal is
`inner ℂ x (A x)`, as in the existing `traceIn`. The trace-class
predicate continues to use the positive left modulus sqrt(A A*),
not a summability premise directly on A's complex diagonal.

This target covers the complex-trace part of the source's
basis-independence assertion. Hilbert–Schmidt and real trace-norm
basis independence have separate targets. This file defines a
proposition, and does not itself prove it or introduce a canonical
trace function. Trace-class ideal laws, products of Hilbert–Schmidt
operators being trace class, and automorphic trace-class operators
remain separate obligations.
