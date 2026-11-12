# Open support pairs and geometric comparisons for the PQ support quotients

Author: Worker 154. Module
`Langlands.Representation.Intertwining.PQSupportOrbit`.

The module constructs the two open orbit-support pairs underlying Renard
VII.3.2 and proves natural isomorphisms from their support-image quotients
to the normalized geometric-lemma pieces. The auxiliary theorem
`Langlands.Aubert.General.RepresentedParabolic.pqSupportComparisons` proves
all the inclusion and subquotient-comparison clauses of the original
`PQSupportGradedStatement`, with its full local-field, arbitrary-parabolic
and independent-universe scope. It does not prove the final identification
at the identity double coset with the identity functor, so it is not a proof
of the whole original target.

## Source and provenance

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VII.3.1–VII.3.2, printed pp.232–233 / PDF pp.238–239, with
the geometric lemma VI.5.1. Registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 reread PDF pp.238–239 while implementing the module.

The provenance is derived. Renard uses the inverse of a Bruhat-refining
order to obtain open orbit prefixes, then identifies the two support
quotients with the same geometric piece. This implementation avoids
choosing a finite ordered enumeration for each comparison. Instead it
constructs each adjacent pair of open invariant supports directly, proves
that their difference is the specified orbit, and uses the published
restriction and extension isomorphism for an arbitrary open orbit pair.

## Topology of the actual supports

`Geometric.leftQuotientDoubleCoset P Q` assigns the actual double-coset
class to each point of `P \ G`. Its well-definedness is proved from the
left-coset relation. `image_preimage_doubleCoset` identifies the image of
a union of double cosets in `P \ G` with the inverse image of its class
set. The class is invariant under right translation by `Q`.

When there are finitely many double cosets,
`isClosed_leftQuotientDoubleCoset_preimage` proves that a set of classes
closed downwards under `BruhatLE` has closed inverse image in `P \ G`.
On `G` the inverse image is the finite union of the closures of its orbits.
The quotient topology then gives closedness on `P \ G`.

For any supplied linear order `o` refining `BruhatLE`,
`initialVanishingSupportPair P Q o ho z` has lower support the complement
of the classes at most `[z]` and upper support the complement of the
classes strictly less than `[z]`. Both excluded sets are downward closed.
Their difference is the orbit of `P z`, expressed in the Library convention
as `cosetOrbit P Q z⁻¹`.

`isClosed_bruhatLT_preimage` proves that the strict Bruhat predecessors of
a class form a closed inverse image. Transitivity gives downward closure;
antisymmetry of the supplied linear refinement prevents a predecessor
from returning to the original class. Consequently
`boundaryVanishingSupportPair` has lower support the complement of the
orbit closure and upper support the complement of its strict boundary.
These are also open invariant supports with difference exactly the same
orbit. All these topological constructions use an actual finite
double-coset quotient and a supplied refinement, without a root
presentation or representation-theoretic assumption.

## Natural quotient comparisons

`OpenOrbitSupportPair.lowerSmoothSupport` and `upperSmoothSupport` are the
actual support subfunctors of smooth induction, with smooth covariance
input. On a compact inducing quotient, `smoothSupportQuotientIso` identifies
their actual quotient with the compact stabilizer-induction orbit piece.
This helper takes the quotient after precomposing the support subfunctors;
its name distinguishes it from `OpenOrbitSupportPair.smoothQuotientIso`
in `Aubert/CorrectedSupportOrbitQuotient`, whose source precomposes the raw quotient.
It transfers the published compact support quotient isomorphism through
the same-function compact-to-smooth comparison. Surjectivity comes from
the published orbit-section extension theorem; it is not assumed here.

For represented parabolics, four private equalities identify these support
spaces with the original `initialVanishingSubfunctor`,
`strictInitialVanishingSubfunctor`, `closureVanishingSubfunctor` and
`boundaryVanishingSubfunctor`. The equality for the boundary uses the
published equivalence between membership of an orbit closure and the
Bruhat relation of its class. `initialVanishingQuotientOrbitIso` and
`boundaryVanishingQuotientOrbitIso` then identify both actual vanishing
quotients with compact stabilizer induction of the normalized inducing
covariance. Naturality holds for every smooth intertwiner.

With target radical points a limit of compact subgroups,
`initialSupportQuotientOrbitIso` and `boundarySupportQuotientOrbitIso`
apply the existing exact normalized target-coinvariant comparison to the
actual support images. Both quotients become the same normalized
coinvariants of the orbit piece. `pqSupportSubquotientIso` composes the
first isomorphism with the inverse of the second.

These generic constructions state explicitly the finite double-coset,
compact inducing-quotient, Hausdorff/sigma-compact ambient and
limit-of-compact-subgroups hypotheses they use. They do not assume a
geometric-lemma piece comparison.

## Unconditional represented-parabolic application

`pqSupportComparisons` supplies all those generic hypotheses from published
unconditional theorems. It has precisely the original support target's
quantifiers and shared-Levi assumption, and proves its first large
conjunct: for every linear refinement and class, the three inclusions,
the natural comparison of the two support-image quotients, and the natural
comparison of the total-order quotient with every supplied intersection
datum at every representative of that class.

The proof obtains a finite enumeration from `representedGeometricLemma`,
compactness from `arbitraryParabolicQuotientCompact`, and second
countability from the canonical rational-point topology. A split component
of the target Levi and `parabolicRootPresentationExistence` show that the
actual target radical is a limit of compact subgroups. Finally
`representedGeometricLemmaOrbitComparison` identifies the normalized orbit
piece with the original datum's `pieceFunctor`. The same original datum,
actions and natural maps are retained, and no finite length, admissibility
or standardness assumption is introduced.

The identity-functor identification in the final conjunct of
`PQSupportGradedStatement` remains open. The module also does not prove
`PQRegularityLemmaStatement`, construct the strict-predecessor filtration
for that Lemma, or derive finite action algebras from finite length.
The original three exact target pairs and their imported closure are
unchanged.
