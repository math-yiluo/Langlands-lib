# Pair-factor comparison for actual irreducible components

Author: Worker 1747.

`Langlands.RankinSelberg.ComponentFactorComparisonStatement` is an internal
supporting statement for the component arguments in the square-integrable
pair-factor problem. It concerns a p-adic field with its canonical topology
and normalized absolute value, a unitary additive character, an additive Haar
measure, and two smooth ambient representations `ξ` and `η` of arbitrary
positive ranks. The representations `π` and `σ` are actual irreducible
components of these ambient representations in the published
`IsIrreducibleComponent` sense: quotients of invariant subspaces by surjective
intertwiners. The field and all four carrier universes are independent.

The statement has two conclusions. First, whenever symmetric gamma-factor
certificates `G` for `(π, σ)` and `H` for `(ξ, η)` exist, `G = H`. Second,
whenever symmetric L-polynomial certificates `P` for `(π, σ)` and `A` for
`(ξ, η)` exist, `P` divides `A` in `ℂ[X]`. The symmetric relations read the
larger rank first, so both conclusions cover either rank order, including
equal rank. No existence of either kind of certificate is asserted.

The provenance is internal. Smooth functional exactness extends each
nonzero functional on an actual component to its ambient representation.
The extension preserves the actual coefficient functions and is nonzero.
The character is locally constant because it occurs in a smooth
representation, and the p-adic upper-unipotent subgroup is a limit of
compact subgroups. The published general
`SubquotientCoefficientModelInclusionStatement` packages the coefficient-model
inclusion with these explicit premises.

For gamma factors, this inclusion is the input to the published
`IsPairGammaFactor.eq_of_model_le`. For L-polynomials, apply inclusion of
the sets of actual coefficient functions to inclusion of zeta-value sets
and then their Laurent spans. The published
`NormalizedGeneratorSpanDivisibilityStatement` identifies this inclusion
with `P ∣ A`, with the displayed direction. Zero functionals contribute only
the zero coefficient function and need no character-locality argument.

This file declares a proposition only. It does not prove the general
coefficient-model statement, supply either factor comparison, prove
multiplicativity or assert a square-integrable pair-factor formula.
