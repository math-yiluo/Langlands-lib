# Strict-rank two-block gamma comparison

This internal deduction concerns a test of rank `r + 1` and the actual ordinary
normalized lower induction of total rank `t + 1`, with `t < r`. The field,
character, supplied self-dual Haar measure, independent carrier universes,
nonzero fixed functionals and three compatible quotient measures are retained.
`StrictTwoBlockSymmetricGammaProduct` asks for complete symmetric gamma
certificates for the two original block pairs and their product on this actual
induced representation. Each certificate retains its full functional and
measure quantifiers through `IsPadicSymmetricGammaFactor`.

`strictComparison_rightWeyl_eq` identifies the actual right multiplier in the
rectangular comparison with the matrix in the unequal-rank functional equation.
For `r = t + (j + k + 1)`, its complementary dimension `j + k + 1` equals `r - t`.
An auxiliary equality eliminates equality of independent dimensions before
comparing the reindexed block sums, so both reindexing proofs agree by proof
irrelevance. Thus the actual right Weyl translation is retained.

`strictTwoBlockSymmetricGammaProduct_of_rationalComparison` assumes the retained
`StrictTwoBlockRationalComparison` and the ordinary Jacquet realization. It
identifies the complete retained first-block certificates with symmetric factors
for the original first block and reversed dual second block. The second uses
the negated character and the same underlying supplied Haar measure. Existence
of the original second block's complete gamma certificate follows from its full
Whittaker type. The actual unequal-rank functional equations imply the reciprocal
relation between that factor and the reflected reversed dual factor.

The model minus-one scalar of the reversed dual second block equals the one of
the original second block, by dual transport and uniqueness on a nonzero
functional. The supplied Jacquet realization gives the product of the two block
scalars for the actual induced model. The polynomial factors used in the
reflected comparison are nonzero because the retained certificates make them
normalized model generators. These facts supply the precise sign and
nonvanishing hypotheses of `reflectedComparison_gammaProduct`, with exponent
`r` as required by the larger test rank.

The actual lower induction has full Whittaker type by the imported normalized
induction result. Its complete gamma certificate therefore exists internally.
Its functional equation, at `j = 0`, `k = r - t - 1`, supplies a nonzero actual
rational integral. Surjectivity of the induced coefficient map represents the
second coefficient by an actual section. Apply the retained rectangular rational
comparison to these coefficients. The transported second-dual functional,
together with the right-Weyl equality above, identifies its reversed integral
with the prescribed dual model integral. Uniqueness of rational continuation
identifies both original and both dual rational functions. Cancelling the
nonzero original rational integral and the nonzero central scalar identifies
the certified whole gamma with the product of the two certified block gammas.

These are internal consequences of the imported rational-comparison, duality,
central-scalar and rational-algebra results. They assert no new literature
translation. The theorem retains its rational-comparison and actual Jacquet
realization premises; the accompanying bound module constructs those premises
on a real twist ray. Neither continuation to zero nor either final closed
dominant-rank target is supplied by this module.
