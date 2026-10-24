# Regularity of normalized reciprocal generators

This module proves the internal algebraic proposition
`Langlands.RankinSelberg.NormalizedGeneratorRegularityStatement`. The theorem
`normalizedGeneratorRegularity` has exactly that proposition as its type.

The implementation first proves that the image of a Laurent polynomial is
regular at a nonzero complex point. Laurent induction writes the polynomial
as an ordinary polynomial times an integral power of the formal variable.
The published `RegularAt.polynomial`, `RegularAt.zpow` and `RegularAt.mul`
lemmas apply because the rational variable evaluates to the nonzero point.

Next, `Submodule.span_induction` transfers regularity from the generating
set to its Laurent span. Zero is a polynomial, sums preserve regularity,
and scalar multiplication is multiplication by the regular image of a
Laurent coefficient.

The normalized-generator span equality puts the reciprocal of `P` in this
span. Its regularity allows evaluation of the product of `P` and its
reciprocal. Normalization makes `P` a nonzero polynomial, so the product is
one. A root of `P` would make its evaluation zero, contradicting this
identity. The auxiliary `eval_zero_ne_zero` uses the constant coefficient
normalization directly.

This proof is derived from the published algebraic definitions and regularity
lemmas. It proves neither rational continuation nor holomorphy of an
integral, and it assumes the normalized-generator relation rather than
constructing a generator.
