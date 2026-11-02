# Rational comparison at strictly dominant rank

This is an internal assembly of the finite-numerator theorem, actual
unequal-rank analysis, reflected-numerator algebra, and the intrinsic
denominator comparison. It does not introduce a new literature translation.
It works at any fixed larger test rank `r` and induced rank `t` with `t < r`.
The block sizes are positive, their ordered carriers may depend on the block,
and all three universe parameters remain independent.

`StrictTwoBlockRationalComparison` retains the two complete
`StrictFirstBlockFactorCertificate` witnesses from the original and reversed
dual block families. Their epsilon units, exponents and original and dual
normalized-generator polynomials are chosen before every complementary row
pair, section or test coefficient. The reversed family uses
`inverseTransposePullback (sigma i.rev)` and the transported second dual
functional of the fixed `reversedDualSectionEquiv`. The supplied self-dual Haar
measure is retained; its negated-character certificate has the same measure.

For every `j,k` satisfying `r = t + (j + k + 1)`, the predicate supplies
rational continuations `R,RD` of the actual original and reversed integrals.
The latter exchanges the row sizes and uses `reversedDualTest`, including its
actual right Weyl translation. Their rational identity is

```text
subst(q inverse)((P1D * P2D).toLaurent * RD)
  = multiplier * (P1 * P2).toLaurent * R,
```

where the Laurent polynomials are mapped to rational functions and `multiplier`
is exactly the image of `clearedProductMultiplierUnit` for the retained
`zeta_i ^ r * c_i` and exponents `d_i`. The predicate also includes finite
clearing of every coefficient pair in the fixed original models. Every
intrinsic normalized generator `P` at every allowed row has a bound
`X ^ e * (P1 * P2) = Q * P`. The integrals in this predicate use the original
finite product of the supplied scalar Haar measure, as in the public
fixed-rank integral wrapper.

`strictTwoBlockRationalComparison_of_numerators` assumes
`StrictTwoBlockFiniteNumerators` explicitly, together with full Whittaker type,
a nonzero larger functional and a nonzero induced inverse-character
functional. It derives the full Whittaker type of the actual lower induced
representation and its actual reversed dual family from the published lower
induction and dual transport theorems.

Surjectivity of the induced model map transfers the finite numerator for a
section to every coefficient in that fixed induced model. A normalized
generator from each retained block certificate proves `P1` and `P2` nonzero.
For each actual section and test, `strictCoefficient_continuationData` supplies
the original and reversed spectral expansions and rational continuations,
including the exact Borel/product-measure identification. The existing
`reflectedNumerators_rationalIdentity` then applies to their common finite
numerator. Finally `strictCoefficient_polynomialDivisibility` uses the
uniform clearing to produce the displayed intrinsic bound.

This pair neither proves the closed first-block analytic statement nor
supplies a final closed dominant-rank gamma or L theorem. Finite numerators
remain an explicit input here. The preceding strict-law unit separately
constructs those numerators above a common opposite-twist bound, conditional
on that independently owned first-block statement. A common-bound wrapper,
identification of the retained block witnesses with full symmetric factors,
continuation to zero and upper induction transport remain later assembly.
