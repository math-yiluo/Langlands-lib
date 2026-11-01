# Normal subalgebras from finite normalization

This file proves
`IntegerFiniteTypeNormalizationReductionStatement.{u}`. The universal
`IntegerFiniteTypeNormalizationStatement.{u}` remains an explicit premise;
this does not prove the unconditional approximation target.

The proof forms `A = ℤ[s]` inside `R` and its normalization `B` in `Frac A`.
The premise makes `B` finite over `A`, hence finite type over ℤ. Integral
closure in a field is integrally closed in its own fraction field. The
inclusion of `A` into `R` extends injectively to `Frac A → Frac R`. An
element of `B` maps to an element integral over `A`, hence integral over
`R`; normality of `R` supplies its preimage in `R`. Injectivity of
`R → Frac R` makes these preimages into an injective ring map `B → R`.
Its image is the desired integer subalgebra. It contains `s` because the
constructed map extends the inclusion of `A`. The equivalence with `B`
transports integral closedness, and finite generation over ℤ supplies
noetherianity.

This implements the internal derivation described by the paired reduction
statement and the published main target's Markdown. Its original-source
provenance is the registered Stacks snapshot
`stacks-normal-finite-type-subalgebras-2026-11-01`: the normalization and
normality construction uses `037B.html`, Lemma 10.37.2. The premise that
normalization is finite corresponds to `032E.html`, Propositions
10.162.15–16 and `032F.html`, Definition 10.161.1, and remains unproved here.
