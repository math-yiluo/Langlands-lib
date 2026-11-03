# Hilbert–Schmidt factorization of a trace-class endomorphism

`Langlands.Analysis.OperatorIdeals.TraceClassFactorizationStatement`
asserts that every bounded trace-class complex-linear endomorphism A of
a complete complex inner-product space E can be written `A = B.comp C`,
where B and C are bounded Hilbert–Schmidt endomorphisms of E. The space
has arbitrary universe and need not be separable or finite dimensional.
Both ideal predicates are the existing existential-basis predicates in
`OperatorIdeals`.

This is an internal intermediate target for the trace construction.
Its source motivation is Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Definition 9.1.1 and the trace definition on
printed p.240 (one-based PDF p.252), the basis-independence assertion
on p.241 (PDF p.253), and Exercises 9.1–9.2 on p.267 (PDF p.279).
Those original passages were read directly. Registered source
`getz-hahn-2024-automorphic-representations` has SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
The complete October 2026 author errata was read and does not amend
these passages; `getz-hahn-2024-errata-2026-10` has SHA-256
`e641ec2a5485443f792935afe5ae4940323755968f784ce290a96d9cd76fc1c2`.

The source assumes separable Hilbert spaces. This broader-scope
factorization is a derived intermediate result, rather than a separate
printed assertion. In the Library's left-modulus convention, put
L = sqrt(A A*) and B = sqrt(L). Positivity identifies the real
diagonal of L with the squared norm of B on each basis vector.
The trace-class witness therefore makes B Hilbert–Schmidt.
Contractive left-modulus factorization gives A = L U; the ideal
law makes C = B U Hilbert–Schmidt, and B squared equals L.

The target asserts only this factorization direction. It does not assert
that all products of Hilbert–Schmidt maps are trace class, trace-norm
estimates, a canonical trace, or an automorphic trace-class theorem.
This file defines a proposition; its proof is a separate obligation.
