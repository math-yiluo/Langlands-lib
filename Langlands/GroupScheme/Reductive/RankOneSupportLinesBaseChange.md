# Rank-one support and root-line data under field extension

This internal derived module packages the three pointwise inputs needed to
construct a rank-one cell: every actual adjoint root is a specified character
or its negative, and both specified weight spaces are linearly isomorphic to
the ground field. `RankOneSupportLines` records exactly these assertions; it
supplies no independent geometric proof of them.

For an arbitrary extension of fields in the same arbitrary universe, an affine
group locally of finite type, a split torus, and any homomorphism from that
torus, `roots_signedPair_baseChange_iff` preserves and reflects the signed-pair
support assertion. The proof uses the published equivalence of actual root
membership under character pullback, its surjectivity on the split character
lattice, and its injectivity to reflect equality and negation.

`rankOneSupportLines_baseChange_iff` combines that equivalence with the
published preservation and reflection of a one-dimensional actual weight space,
`weightSpace_line_baseChange_iff`, applied to the character and its negative.
No reductivity, maximality, root datum, reducedness, or algebraic closedness is
assumed in these field-extension lemmas. The content is derived from the
published actual-root and actual-weight scalar-extension comparisons.

This module is the descent component of the independent root-cell
construction, whose conditional cell construction is
`splitRankOneRootCell_of_supportLines` in `Reductive.IndependentRootCellReduction`.
This helper does not prove the final root-cell statement or the independent
geometric input.

The module also proves the equivalence between the two structural
interfaces. The forward direction restricts the field quantifier. For the
reverse direction, `splitRankOneRootSupportLines_of_algClosed` base changes the
connected reductive group, its prescribed split maximal torus, and its supplied
actual root datum to an algebraic closure. Connected reductivity and maximality
are preserved by the existing structural base-change results. The canonical
actual root-set equivalence preserves pairwise integral dependence; the actual
root-datum base-change theorem preserves its root, coroot, pairing, and
normalizer-reflection clauses. Applying the explicit algebraically closed input
to this transported datum gives the three local assertions, and the pointwise
field-extension equivalence descends them to the original field. The proof
changes neither the universe nor the prescribed torus or root datum.

`splitRankOneRootSupportLines_iff_algClosed` records the resulting logical
equivalence. Its geometric premise is explicit and remains unproved here.

The development type/value audit on 17 November 2026 recursively traversed the
used constants of each declaration's type and body, including opaque bodies.
It reported the following closures, with zero matches against every excluded
constant below:

| Declaration (namespace `Langlands.GroupScheme`) | Reached constants |
| --- | ---: |
| `RankOneSupportLines` | 24507 |
| `roots_signedPair_baseChange_iff` | 30971 |
| `rankOneSupportLines_baseChange_iff` | 34797 |
| `algClosedRankOneRootSupportLines_of_statement` | 26270 |
| `splitRankOneRootSupportLines_of_algClosed` | 109311 |
| `splitRankOneRootSupportLines_iff_algClosed` | 109313 |

The audited excluded constants, all in namespace `Langlands.GroupScheme`, were
`ParabolicDynamicStatement`, `RegularCocharacterBorelStatement`,
`RankOneSolvableObstructionStatement`, `RankOneBorelDynamicStatement`,
`RankOnePositiveRootUniquenessStatement`, `parabolicDynamic`,
`regularCocharacterBorel`, `rankOneSolvableObstruction`, `rankOneBorelDynamic`,
`rankOnePositiveRootUniqueness`, `splitRankOneRootCell`, `splitRootLieLine`,
`prescribedBorelProjectiveCurveData`,
`regularSignedCurveUnipotentDataOfIsConnectedReductive`,
`rankOne_rootTangent_le_one_of_projectiveBorelInputs`, `rootDatumExistence`,
`rootReducedness`, `reductiveGeometricReductivity`, `absoluteBruhatCovering`,
`steinbergBigCell`, and `isParabolicSubgroup_of_range_eq_dynamicParabolic`.
This is a declaration dependency audit, distinct from an import-graph audit.
The imported positive-root base-change module contains additional excluded
statements, but only its independent actual-root pairwise-dependence transport
is used by this proof. The audit does not discharge the explicit algebraically
closed geometric premise.
