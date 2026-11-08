# Finite conductor support for actual global additive characters

Worker 1692 supplies internal adapters from an actual global additive character,
trivial on the diagonal, to the lattice arithmetic proved by Worker 1798 in
`Hecke.AdelicLattice`. The number field has unrestricted universe `u`. Every
finite local component and every unit-valued real and complex scale is supplied
with exactly the component predicates of the global functional-equation target.

`additiveProductFormula_of_global` reindexes the supplied subtype families into
`mixed_additive_product_formula`. Its conclusion is the precise positive-sign
`Hecke.AdditiveProductFormula`: for each field element all but finitely many
finite values are one, and their finite product times the mixed trace character
is one. The finite set may depend on that element.

`finite_additiveConductor_support` combines this formula and the nonvanishing
of the supplied scales with `Hecke.finite_setOf_additiveConductor_ne_zero`.
The remaining input to that arithmetic theorem, nonnegative conductors outside
a finite set, follows from continuity of the actual global character through
`eventually_additiveConductor_nonneg`. The arithmetic theorem uses the full
trace-dual ideal lattice and strong approximation to exclude positive conductor
at almost every place; no topological Pontryagin pairing equivalence is assumed.

`additiveConductorDivisor` bundles the original conductor values as a finitely
supported integer vector, with its exact evaluation theorem.
`exists_finset_additiveConductor_eq_zero` takes its support as the exceptional
set. `exists_finset_finiteEpsilon_eq_one` applies the existing local epsilon
normalization and finite multiplicative ramification theorem. For every supplied
self-dual local measure, the exact finite epsilon expression in the global target
is therefore one at every spectral parameter outside a single finite set.

This unit proves the conductor and epsilon conclusions under the supplied actual
local data. It does not construct those local data, a global pairing equivalence,
meromorphic continuation or the global functional equation.
