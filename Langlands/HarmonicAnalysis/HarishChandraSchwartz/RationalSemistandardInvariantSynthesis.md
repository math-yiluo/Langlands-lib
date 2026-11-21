# Waldspurger's synthesis on invariant spectral families

Waldspurger (2003), VI.3, printed pp. 305–306, defines `κ` as the
restriction of his weighted synthesis `κ̃`. `GlobalSynthesis.invariantSynthesis`
composes the actual `GlobalSynthesis.schwartzSynthesis` with the inclusion
of `rationalSemistandardThetaInvariantSections`. It takes the exact
`SchwartzMembershipStatement` and its geometric and source-compact
inputs. Evaluation is the weighted sum of the actual source packets on
the underlying smooth family. Each integral uses its existing pointwise
integrability proof.

`GlobalSynthesis.FactorizationStatement` is the function equality in
VI.3.2 before codomain restriction. It compares the actual weighted
synthesis with evaluation on `Average.smoothAverage`. The typed
factorization follows by equality of the underlying functions, using
`Average.InvariantImageStatement` to construct the actual projector.
The raw factorization requires transport of the source packet and
weight followed by reindexing the finite sums.
