# Constructed generic p-adic L-factors in either rank order

Author: Worker 31.

`genericSymmetricLPolynomial` constructs an actual normalized polynomial, and
`genericSymmetricLFactor` constructs an actual unit of `RatFunc ℂ`, for generic
representations of any two positive ranks over a p-adic field. The field and
the two representation carriers have independent universes. The topology is
the canonical topology of the supplied `PadicField`; the nontrivial unitary
additive character and additive Haar measure are supplied. The measure need
not be self-dual. The ranks include rank one and require no ordering hypothesis.

Both definitions branch on `n ≤ r`, where the input ranks are `r+1` and `n+1`.
In that branch they use `genericPairLPolynomial` and `genericPairLFactor`
in the original order. Otherwise they apply the same constructions with the
two representations exchanged and proof that `r ≤ n`. Each exchanged call
also exchanges the carrier universes and genericity hypotheses. At equal rank
the original order is retained. This implements precisely the convention of
the existing `IsPadicSymmetricLPolynomial` relation.

The four `_of_le` and `_of_lt` lemmas identify these definitions with the
corresponding larger-first construction. The polynomial specification
`genericSymmetricLPolynomial_isPadic` follows in each branch from the complete
`genericPairLPolynomial_isPadic` relation. In particular, a compatible quotient
measure exists and the same polynomial characterizes the zeta-integral
fractional ideal for every compatible quotient measure and every allowed
unequal-rank block. No empty measure quantifier supplies the specification.

`genericSymmetricLPolynomial_coeff_zero` proves constant coefficient one.
`genericSymmetricLPolynomial_eq` uses uniqueness of the existing symmetric
relation to compare the constructed polynomial with any certified polynomial.
`coe_genericSymmetricLFactor` gives the reciprocal of the polynomial embedded
in `RatFunc ℂ`, and `genericSymmetricLFactor_eq` gives this formula for any
polynomial satisfying that relation. The unit is the existing actual
larger-first unit in the selected rank order; it is not an arbitrary function
chosen independently of the integral relation.

The source is Jacquet, Piatetski-Shapiro and Shalika, *Rankin–Selberg
Convolutions* (1983), registered as `jpss-1983-rankin-selberg`, SHA256
`d9feed6388ca5acf02ecc6a8cce984871a7c28f062ff441e45a71fa2d8962245`.
Theorem 2.7(i)–(ii), printed pp.390–391, gives the normalized reciprocal
generator with formal variable `X=q^(-s)`. Section 2.12, printed p.403,
defines the opposite-rank factor by the larger-first factor. The original printed p.403 (retained PDF page38) was visually read directly
for this construction: its unequal-rank convention is the branch implemented
here. Theorem 2.7 was also directly read for the preceding larger-first
construction. No JPSS-specific erratum was found among the project literature
and published errata-note filenames checked.

This is derived composition and specialization of the existing
[PadicPairLFactor](PadicPairLFactor.md) constructors and the rank-order
equivalences and uniqueness from [PadicPairFactors](PadicPairFactors.md).
The proof supplies no new analytic input. Equal-rank symmetry as a factor
law, changes of additive character, epsilon and gamma constructions, and
classification-based nongeneric extensions are separate results.
