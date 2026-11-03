# The two possible standard associates of a maximal root subset

Worker 167. This is an internal finite-root deduction for the actual rational
point families. It uses the published `rootAssociation` predicate and Coxeter
proofs, and introduces no representation-theoretic premise.

`MaximalRootAssociationDichotomy` names the proposition that every actual
associate of each maximal standard subset is either that subset or its specified
associated subset. `maximalRootAssociationDichotomy_of_rootSignComparisons`
proves this proposition from the three explicit comparisons below, by applying
`rootAssociation_eq_or_eq_associatedSubset` to every subset and representative.
The proposition is a proved conclusion, rather than an extra input to the
rational self-association target.

`rootAssociation_isMaximalStandard` proves that actual root association preserves
`IsMaximalStandard`: a subset consisting of all simple-root labels except one.
Association preserves cardinality and properness by `rootAssociation_card_eq`
and `rootAssociation_ne_univ`. Choosing any label omitted by the target subset,
cardinality then identifies that subset with the complement of that label.

`rootAssociation_eq_or_eq_associatedSubset` proves that an actual association
from a maximal standard subset `J` to `K`, represented by an actual rational
point `n`, forces `K = J` or `K = associatedSubset actual J`. The Coxeter group
is the actual normalizer modulo the full centralizer of the torus points, and
its simple labels are the literal `SimpleRoot i ν`. The hypotheses are
`RootLengthComparison`, `PositiveSimpleReflectionComparison`, and
`minimalityLengthCriterion`, together with finiteness of the simple-root type
and the actual Weyl group. All are already present in the original rational
rank-one self-association target. No assumption that `K` is proper is needed:
association with maximal `J` already implies it. The result does not require
`actualLeviWeylIdentification` or `associatedSubsetLaws`.

The implemented proof takes the quotient class `w` of the supplied normalizer
point. If this class is the identity, its character action is the identity and
injectivity of `rootSet` gives `K = J`. Otherwise, the association and
`rootAssociation_inv` show that `w` maps `J` into the actual simple roots in `K`
and `w⁻¹` maps `K` into those in `J`. Simple roots are positive, so
`RootLengthComparison` gives right ascents on both subsets and the displayed
minimality criterion makes `w⁻¹` a left `J`-minimal representative.

A nonidentity Coxeter element has a right descent. Thus the set of right ascents
of `w⁻¹` is proper. It contains the maximal subset `K`, hence equals `K`.
`PositiveSimpleReflectionComparison` converts the actual root map on this set
to `MapsIntoSimple`. The published `longestSurvivor_proof` now identifies `w⁻¹`
with the specified `longestRep actual J`. Finally,
`rootSet_rootSimpleImage_of_mapsIntoSimple`,
`rootSimpleImage_eq_simpleImage_of_positive`, and `rootSet_injective` identify
`K` with `simpleImage actual (longestRep actual J)⁻¹ J`, which is the definition
of `associatedSubset actual J`.

The private finite-set helper uses only the cardinality of a maximal proper
subset; the private root-map helper unpacks the root-set image equality. Empty
simple-root types are allowed, with the maximality hypothesis then impossible.
The ambient field, torus, affine group scheme, monomorphism and point-normalizer
and point-centralizer comparisons have the scope of `rootAssociation`; no
connectedness, reductivity, local-field, topology or representation hypothesis
is needed for this stronger conditional finite-root result.

The provenance is internal: the new argument combines the published elementary
association laws, the actual root-sign interfaces and the proved intrinsic
longest-survivor criterion. No external literature assertion is added. The
Coxeter criterion depends on the published exchange and minimality proofs, and
not on Langlands classification, character independence, a geometric lemma,
adjointness or cuspidal-support theory. This helper does not prove that
reducibility forces `associatedSubset actual J = J`, actual Levi normalization,
or the full `RationalRankOneSelfAssociationStatement`.
