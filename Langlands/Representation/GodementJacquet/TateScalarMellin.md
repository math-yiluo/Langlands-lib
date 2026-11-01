# Uniform scalar Mellin data for the Tate base

`ScalarMellinAnalyticData` records the actual multiplicative-Haar integrals of
all Schwartz–Bruhat tests against one finite function, with positive integral
weight. It retains one convergence half-plane for every test, rational
continuation in the actual spectral variable, and a common Laurent denominator
for all continuations of all tests. The callable integrand, integral and value
set are `scalarMellinIntegrand`, `scalarMellinIntegral` and
`scalarMellinRationalValues`.

`scalarMellinAnalyticData_finiteFunction` proves this data for every supplied
p-adic field and topological data, continuous function with finite-dimensional
translation span, and positive integral weight. This is a derived internal
strengthening of the published one-variable Mellin interface, retaining a
uniformity already present in its implemented shell proof.

The rationality and denominator clauses apply
`Langlands.RankinSelberg.oneVariableMellin` unchanged. For uniform convergence,
`finiteFunctionShellSeries` gives a real growth bound `B ≥ 1` before choosing a
test. Positivity of the residue-cardinality logarithm gives one threshold where
`B * ‖(q^(-s))^m‖ < 1`. The normalized absolute value on a nonzero scalar
is `q^(-ord(a))`; complex-power identities therefore identify the scalar Mellin
integrand with the integrable shell integrand. The shell convergence conclusion
applies to every test on this same half-plane.

The private complex-power and spectral-bound proofs adapt the corresponding
helpers in Worker 656's published `OneVariableMellinProof`, which in turn
attributes their elementary power argument to Worker 235's
`RamifiedFiniteFunctionMellinProof`. Those adapted proofs, rather than any new
original-source assertion, are the provenance of this internal strengthening.
The imported shell theorem is Worker 277's published result. The mathematical
context and original-source locators for the one-variable argument remain in
the unchanged `OneVariableMellinProof.md`; no Fourier equation or normalized
generator is asserted here.
