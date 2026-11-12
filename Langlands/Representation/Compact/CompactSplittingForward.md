# Finite fixed-level strata and compact-category splitting

Author: Worker 88. `compactCategoryDecomposition_of_finite_strata` is the
forward implication of Renard IV.1.7 Proposition, printed pp.95–96 / PDF
pp.101–102. The original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The helper is derived internal infrastructure. It takes a Hausdorff locally
compact totally disconnected topological group with a Borel structure and
left Haar measure, and the finiteness of the exact published fixed-level
stratum at every compact open subgroup. Group and carrier universes remain
independent. The final target retains its stronger regular two-sided Haar
and sigma-compactness premises; none is weakened or added by the entry proof.

Choose the intrinsic compact-class projector for every class and ambient
smooth object using the published unconditional isotypic/annihilator
complement theorem. The existing `isotypicProjectorOfIsCompl` constructor
provides idempotence, exact range and kernel, and naturality. Schur separation
in `isotypicProjectorFamilyOfIsCompl_orthogonal` gives pairwise orthogonality.

Every smooth vector `x` is fixed by an open subgroup `L`; choose compact open
`K ≤ L`. A class outside its fixed-level stratum has no nonzero `K`-fixed
vector. The published annihilator-containment theorem puts `x` in that
class's projector kernel. By (KF) only finitely many component projectors
can therefore be nonzero on `x`. The published `pointwiseFiniteSum` constructs
the sum as an actual equivariant linear endomorphism. Its algebra gives
idempotence from the individual idempotence and orthogonality laws, and its
covariance theorem proves naturality for every smooth morphism. Its range
is exactly the supremum of the component ranges, hence the published total
intrinsic compact-isotypic subrepresentation.

This total projector fixes every vector of a smooth object exactly when
the object has compact coefficients. If it fixes `x`, that vector lies in
the total isotypic part; the published compact-coefficient vector containment
gives compact ambient coefficients for `x`. Conversely, the published
`totalIsotypicSubrepresentation_eq_top_of_compactCoefficients` makes the
range top on a compact object, and a surjective idempotent fixes every vector.
The proof applies this criterion to irreducibles as required by the next step.

Finally, the published
`SmoothRep.categoryDecomposition_of_natural_idempotent` turns this natural
idempotent and its irreducible test into the exact A.IX decomposition for
the all/no-compact irreducible-subquotient factors. That theorem constructs
actual range/kernel coproduct cofans with their full colimit universal
properties and proves off-diagonal Hom vanishing via a nonzero image and
an actual irreducible subquotient. Thus the conclusion is the published
`Renard.IsCategoryDecomposition`, for arbitrary smooth objects and every
actual irreducible subquotient, as in the main target.
