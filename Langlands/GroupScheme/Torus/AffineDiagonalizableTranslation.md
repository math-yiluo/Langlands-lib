# Translation by a diagonalizable subgroup

Internal adapters for the construction of affine quotients by central
multiplicative-type subgroups over arbitrary bases. Over an arbitrary scheme S, the
translation graph of a homomorphism H → G sends (h,g) to (g,i(h)g). It factors
as the product of the inclusion with the identity, followed by the square
automorphism (x,y) → (y,xy), whose inverse is (x,y) → (yx^{-1},x).
Consequently a closed subgroup has a closed translation graph. No smoothness,
normality, or affineness is needed for this fact.

Over Spec R with G affine, `ofTranslation` defines the natural character action
on the actual coordinate algebra points, using the published comparisons with
scheme points. Its identity, associativity and naturality follow from the group
law and the character-point comparison. A separate general adapter proves that
any `CharacterAction.Action` yields the coefficient identities of
`StronglyGraded.IsGrading`: evaluation at the trivial character is the sum of
coefficients, and the existing coassociativity theorem gives homogeneity.

Provenance: internal scheme/coordinate adapters toward the affine translation
quotient in SGA 3, Exposé VIII, Gille–Polo recomposition of 8 November 2009,
§§4–5, particularly Theorem 5.1. Registered source
`sga3-expose-viii-gille-polo-2009`, SHA-256
`06e43e0571d411cc5579975778fcc03c8ecaa67189248d1a053e61dc653af510`.
The graph factorization and comparison proof are internal. This module does not
identify the graph coordinate ring map or construct the quotient scheme.
