# Reflected ratio data from gamma multiplicativity

This derived supporting module constructs the rational comparison used in the
tempered product argument. It uses full Whittaker type of every block, certified
original L-polynomials and certified polynomials for the actual inverse-transpose
pullbacks at the character scaled by minus one. It does not construct the dual
certificates or assert a pole bound.

`TemperedLFactorGamma.ReflectedRatioData δ P PD B BD` stores a complex unit `c`,
an integer `a`, and the rational-function identity

```
B(X) / BD(δ/X) = (c X^a) P(X) / PD(δ/X).
```

Here each polynomial is mapped into `RatFunc ℂ`, and reciprocal substitution is
the published algebra homomorphism `RationalReflection.subst δ`. The type does
not assume that these polynomials are normalized or nonzero. Its identity is
interpreted in the rational-function field, including its totalized division.

`epsilon_exists_of_whittakerType` extracts epsilon data from the published
`whittakerTypeGammaConstructionInput`, choosing the larger-rank-first input in
each rank order. This works for full-type normalized inductions, without a
separate irreducibility or genericity assumption on those inductions.
`symmetricGammaFactor_swap` unfolds the symmetric predicate in strict rank
orders and applies the published full-type gamma exchange at equal rank, at the
same character and supplied additive Haar measure.

`rationalGammaExpression_prod` proves that the explicit gamma expression
multiplies over any finite index type. The coefficient units multiply, the
integer exponents add, and the original and reflected dual polynomial factors
multiply. The proof uses preservation of products by the polynomial maps and
finite-set induction for the integer powers of the nonzero rational variable.
`reflectedRatio_of_gammaExpression_eq` then cancels a nonzero epsilon monomial:
if the product expression with coefficient `c₁` and exponent `a₁` equals the
induced expression with `c₀,a₀`, the ratio coefficient is `c₀/c₁` and its exponent
is `a₀-a₁`. The cancellation requires no nonzero polynomial denominator premise.

`gamma_doubleProduct` applies the published `gammaMultiplicativity` twice.
Full Whittaker type passes to each actual canonical normalized induction by
`normalizedProductWhittakerType`. Symmetric gamma exchange aligns the outer
certificates, and uniqueness identifies every intermediate factor with the
product supplied by the corresponding second-family application.

`nonempty_reflectedRatioData` retains three independent universes and both rank
orders. It takes certificates for `P` on the actual two induced representations,
`Q i j` on every block pair, `PD` on the actual inverse-transpose pullbacks of
those inductions, and `QD i j` on the block pullbacks. It constructs epsilon
data for the induced pair and every block pair, applies
`symmetricGammaExpression` to the gamma certificates, and multiplies the block
expressions using the finite-product lemma. The resulting data has
`B = ∏ i, ∏ j, Q i j` and `BD = ∏ i, ∏ j, QD i j`, with coefficient equal to the
induced epsilon coefficient divided by the product of block epsilon
coefficients, and exponent equal to the analogous difference.

The provenance is internal composition of the cited published Lean results and
elementary field algebra. This module supplies the rational comparison only.
Normalized residual factorizations, actual dual certificate existence,
square-integrable genericity, original and dual pole bounds, and the final use
of reflection rigidity remain obligations of the tempered theorem assembly.
