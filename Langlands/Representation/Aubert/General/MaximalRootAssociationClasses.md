# Weyl classes of maximal actual root associations

Worker 167. Internal strengthening of `MaximalRootAssociation`: an element
`w` of the actual normalizer modulo the full centralizer carries a maximal
standard root subset `J` onto a standard root subset `K` only in the two cases
`w = 1, K = J` or `w = (longestRep actual J)⁻¹,
K = associatedSubset actual J`.

`MaximalRootAssociationClassDichotomy` names this proposition, and
`maximalRootAssociationClassDichotomy_of_rootSignComparisons` proves it from
`RootLengthComparison`, `PositiveSimpleReflectionComparison` and
`minimalityLengthCriterion`. The pointwise proof is
`rootImage_class_eq_one_or_eq_inv_longest`. The hypotheses and universes are
those of the published maximal-association helper: an arbitrary field in
universe `u`, an affine group scheme, a monomorphic torus inclusion with
point-normalizer and point-centralizer comparisons, and finite actual
simple-root and Weyl types. Empty simple-root types are allowed and have no
maximal subset. No representation carrier or second universe occurs in this
finite-root unit.

The implemented proof retains the quotient equality constructed inside the
published maximal-association argument. Choose a lift solely to invoke
`rootAssociation_isMaximalStandard`. An identity class fixes the root set.
For a nonidentity class, the forward and inverse root images are simple and
positive. The root-length comparison makes the inverse left `J`-minimal.
Its ascent set contains maximal `K` and is proper because a nonidentity
Coxeter element has a descent. Thus its ascent set is exactly `K`. The
positive simple-reflection comparison and `longestSurvivor_proof` identify
the inverse with `longestRep actual J`. The root-image comparison then gives
the associated subset. This is a deduction from the published definitions
and intrinsic Coxeter proofs, with no new literature assertion.

`rootImage_eq_of_mapsIntoSimple_of_card` proves that
`RootMapsIntoSimple i ν hN hZ w J K` gives equality of the actual root
images whenever `J.card = K.card`. Choose the target simple-root label for
each element of `J`. The actual character action is injective, so this map
between the two finite subtypes is injective. Equal cardinalities make it
surjective by `Fintype.bijective_iff_injective_and_card`, giving the reverse
image containment. This helper needs no finite ambient simple-root or Weyl
type, no Coxeter system, and no root-sign comparisons.

`rootImage_eq_of_full_intersection` applies that helper to a representative
`w` minimal for `(K,J)` and a full source intersection
`intersectionSubset actual K J w = J`, again with equal source and target
cardinalities. Minimality and `hLength` give positivity of the actual
images of the source roots. The full intersection and
`exists_conj_simple_eq_of_isMinimal` give conjugation of each source simple
reflection to a target simple reflection. The positivity-sensitive
`rootMapsIntoSimple_iff_of_positive` turns this reflection statement into
the actual root statement. In particular, reflection conjugation alone is
not used as a root-sign assertion.

The last two results give the unique possible full-intersection
representatives when `J` is maximal and
`J ≠ associatedSubset actual J`:

- `full_self_intersection_iff_eq_one`: for `w` minimal for `(J,J)`,
  its source intersection is all of `J` if and only if `w = 1`.
- `full_associated_intersection_iff_eq_inv_longest`: for `w` minimal for
  `(associatedSubset actual J,J)`, its source intersection is all of `J`
  if and only if `w = (longestRep actual J)⁻¹`.

For the forward directions, full intersection gives an actual root-image
equality and the class dichotomy excludes one alternative by the displayed
inequality. In the associated case, `associatedSubsetLaws_proof` supplies
the equal cardinalities. For the reverse directions, the identity or the
same published associated-subset laws give `MapsIntoSimple`; membership
of the corresponding simple reflections in the target standard subgroup
then proves full intersection. These are equivalences conditional on the
displayed minimality, not assertions about arbitrary Weyl elements.

The declaration dependencies used by these deductions are the published
actual-root action, `rootAssociation_isMaximalStandard`,
`rootSet_injective`, `rootSet_rootSimpleImage_of_mapsIntoSimple`,
`rootSimpleImage_eq_simpleImage_of_positive`,
`rootMapsIntoSimple_iff_of_positive`, the intrinsic
`longestSurvivor_proof`, `exists_conj_simple_eq_of_isMinimal`,
and `associatedSubsetLaws_proof`. Their uses above explain the internal
provenance. No classification, character independence, geometric lemma,
adjointness, or cuspidal-support theorem is used in the implemented
deduction.

This finite-root unit does not construct a geometric-lemma filtration,
prove a representation isomorphism or simplicity, or prove the host
`RationalRankOneSelfAssociationStatement`.
