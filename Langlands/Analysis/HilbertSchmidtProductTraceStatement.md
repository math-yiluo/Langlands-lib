# Complex diagonal sums of Hilbert–Schmidt products

`Langlands.Analysis.OperatorIdeals.HilbertSchmidtProductTraceStatement`
concerns actual bounded complex-linear maps B from E to F and C from F
to E, each satisfying the existing existential-basis Hilbert–Schmidt
predicate. The spaces are complete complex inner-product spaces in
independent arbitrary universes. Their supplied Hilbert bases b and d
have independent arbitrary index universes.

The target asserts summability of the norms of the complex diagonals of
`C.comp B` in b and `B.comp C` in d, and equality of the existing
complex sums `traceIn b (C.comp B)` and `traceIn d (B.comp C)`.
Mathlib's complex inner product is linear in its second argument:
the diagonal is `inner ℂ x (A x)`. This is the convention already used
in `OperatorIdeals.traceIn`. No total sum outside the stated absolute
summability conclusions is interpreted as a trace.

This is an internal intermediate result for constructing the trace.
Its motivating source is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and the trace definition on
printed p.240 (one-based PDF p.252), the independence assertion on
p.241 (PDF p.253), and Exercises 9.1–9.2 on p.267 (PDF p.279).
Those original passages were read directly. The registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata was read and does not amend
these passages; `getz-hahn-2024-errata-2026-10` has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source works with separable endomorphism spaces and asks for
trace-class membership of a product of Hilbert–Schmidt operators.
This target is a derived rectangular diagonal-sum lemma, with broader
index scope. It neither states nor proves that trace-class membership.
For its internal rationale, expand the diagonal through the other
Hilbert basis. The coefficient array is
`inner b_i (C d_j) * inner d_j (B b_i)`. Parseval and Hilbert–Schmidt
basis independence make both squared coefficient arrays summable.
The norm of their product is bounded by the sum of their squared
norms. Absolute summability permits exchange of the two index sums;
the Hilbert-basis inner-product expansion identifies them with the
two complex diagonals.

This file defines a proposition target. Its exact proof, trace-class
membership of products, trace-class diagonal independence, canonical
trace and automorphic trace-class constructions are separate obligations.
