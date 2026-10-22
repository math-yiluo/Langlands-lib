# Gauss points and power bounds for strict Tate algebras

Author: Worker 56, building on Worker 36's actual restricted-series construction.

The coefficient norm is attained because the coefficient sequence vanishes at
infinity: above any positive threshold there are only finitely many coefficients.
The finiteness, attainment and first-maximum lemmas work over any ultrametric
normed commutative coefficient ring. Among the coefficients of maximal norm
choose the first in a monomial order.
The remaining results specialize to a normed field.
For two series, the sum of the chosen exponents has exactly one convolution term
of maximal norm. Every other pair has an earlier exponent in at least one factor.
The strong triangle inequality therefore proves multiplicativity of the Gauss
norm. This gives an actual bounded multiplicative seminorm, the Gauss point.

For finitely many variables, evaluation at that point identifies the condition
that every spectrum point has value at most one with the coefficient norm being
at most one. Submultiplicativity then bounds every power by one. The coefficient
field may have trivial valuation, and completeness is not needed for these
results. No reduction or finite-dimensional assumption is used.

This is the unquotiented Tate-algebra case, not the requested theorem for all
closed-ideal affinoid quotients. The construction of suitable monic relations for
general quotients, Noether normalization, and the corresponding spectral bound
is developed in separate modules. They are not assumed in this module.

Source correspondence: Berkovich's course notes headed "2. Affinoid algebras",
hosted at
https://math.huji.ac.il/~temkin/teach/math738/Affinoid_algebras.pdf,
section 2.1, page 1 (multiplicativity of the coefficient norm), and
Proposition 2.6.5, page 12 (the general power-boundedness result for which this
is supporting infrastructure). The operator supplied the exact 14-page PDF,
now read in full, with pages 1, 3, 6, 11 and 12 also inspected visually.
It identifies itself as notes of part of Vladimir Berkovich's course; the
note-taker and publication date are not identified. Its PDF metadata is dated
2011-02-28. Registered source:
`provided-5bef167efa5132f5b1d86ebccc155f5235889dda5b0a146526cec8113e450942`;
content SHA256
`c6d0cbc658fd9753a63afca9fe3025a4ca948f4a46d5899493f2753587ca0d18`.
Retained file:
`literature/Retained original of Berkovich's Affinoid algebras course notes (14 pages).pdf`.

The precise implementation uses Mathlib's
`MvPowerSeries.antidiagonal_dominant` for the final strong-triangle argument.
It proves, rather than assumes, the required dominant coefficient.
Its internal dependencies are the actual `TateAlgebra` construction (Worker 36,
with Worker 56's coefficient generalization) and `Spectrum.Definitions`.
The division proof uses the coefficient norm-attainment lemmas from this
module; the spectral proof also uses its Gauss point.
