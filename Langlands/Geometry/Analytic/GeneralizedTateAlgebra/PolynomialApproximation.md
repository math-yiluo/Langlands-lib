# Monomial expansion and polynomial density at positive polyradii

Author: Worker 105.

`Langlands.Analytic.GeneralizedTateAlgebra.polynomialApproximation`
proves the entire published `PolynomialApproximationStatement r K`.
The variable type and coefficient ring have independent universe levels.
The only coefficient assumptions are `NormedCommRing K` and
`IsUltrametricDist K`; the radii are those of `PositivePolyradius`.
In particular, the proof assumes neither completeness nor finitely many
variables, and imposes no norm-one, nonzero-ring, nontrivial-valuation,
or value-group condition. Empty variable types and zero coefficient rings
are included.

This is an internal derived proof from the published weighted restricted
series construction and its norm bounds. The mathematical provenance of
the construction and target is recorded in
[Definitions.md](Definitions.md) and
[PolynomialApproximationStatement.md](PolynomialApproximationStatement.md),
authored by Worker 56. No separate assertion from the original literature
is invoked here. The Lean proof follows the direct coefficient-decay
argument proposed in the target documentation, without using a
completeness theorem.

`seriesAlgHom` packages the existing underlying-series inclusion as an
algebra homomorphism. `polynomialMap` is exactly `MvPolynomial.aeval` at
the actual coefficient-one coordinate monomials, as specified by the
target. Equality of algebra homomorphisms on the polynomial variables
identifies its composite with `seriesAlgHom` with Mathlib's canonical
polynomial-to-series inclusion. Consequently `series_polynomialMap` and
`coeff_polynomialMap` preserve the entire underlying series and every
polynomial coefficient. `polynomialMap_monomial` identifies each
polynomial monomial with its actual restricted-series monomial.

For a finite set of finitely supported exponents, `truncation` is the
finite sum of the corresponding coefficient monomials of the given
element. `coeff_truncation` shows that its coefficient is the original
coefficient on that finite set and zero elsewhere.
`norm_truncation_sub_le` is the quantitative estimate: a nonnegative
uniform bound on the weighted norms of the omitted coefficients bounds
the norm of the truncation minus the element. Its proof applies the
published `norm_le_iff`; retained coefficients cancel, and omitted
coefficients differ only by a sign.

To prove `tendsto_truncation`, fix a positive epsilon. Restrictedness
says that the weighted coefficient norms tend to zero along the
cofinite filter. Therefore the exponents for which the distance to zero
is not less than half epsilon form a finite set. Any truncation whose
index set contains this exceptional set has remainder norm at most half
epsilon, hence less than epsilon. This proves convergence of the net
indexed by all finite exponent sets ordered by inclusion.
`hasSum_monomials` is exactly this convergence in Mathlib's default
unconditional `HasSum` convention. The argument also applies when the
exponent type is finite; it does not require a nontrivial cofinite filter.

Finally, `polynomialMap_sum_monomials` exhibits each finite truncation as
the evaluation of the polynomial formed from the same finite set of
coefficients. `denseRange_polynomialMap` uses convergence of these
truncations to place every algebra element in the closure of the
evaluation map's range. The closing theorem pairs this density with
`hasSum_monomials`, with exactly the published target as its conclusion.

The helpers expose polynomial coefficient compatibility, finite
truncations, a uniform remainder estimate, norm convergence, and density
for downstream constructions. This contribution does not prove
completeness or any quotient or rational-domain theorem.
