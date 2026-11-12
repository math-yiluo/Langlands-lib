# Natural inclusions of the PQ support subspaces

Author: Worker 154. Module `Langlands.Representation.Intertwining.PQSupportInclusions`.
The primary construction `pqSupportInclusionMaps`, in namespace
`Langlands.Aubert.General.RepresentedParabolic`, gives the three natural
same-function inclusions of Renard VII.3.2. The module also proves their
pointwise subrepresentation inequalities in `pqSupportInclusions`.

## Source and correspondence

David Renard, *Représentations des groupes réductifs p-adiques*, French version
of 9 July 2026, VII.3.1–VII.3.2, printed pp.232–233 / PDF pp.238–239;
registered source `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 154 read these two PDF pages.

The three maps have source and target, respectively:

1. `initialVanishingSubfunctor → strictInitialVanishingSubfunctor`,
   Renard's `F̃^{⪯w} → F̃^{≺w}`;
2. `strictInitialVanishingSubfunctor → boundaryVanishingSubfunctor`,
   Renard's `F̃^{≺w} → F̃^{<w}`;
3. `closureVanishingSubfunctor → boundaryVanishingSubfunctor`,
   Renard's `F̃^{≤w} → F̃^{<w}`.

They are natural transformations between the actual subrepresentation functors
of normalized induction restricted to Q. Each map preserves the underlying
function. The construction works for any linear order on the actual double
cosets refining the published Bruhat relation.

## Implemented argument and internal provenance

`Geometric.mul_mem_closure_doubleCoset` proves left P-invariance of a
double-coset closure by continuity of left multiplication. Together with the
published right Q-invariance, this gives
`mem_closure_doubleCoset_iff_bruhatLE`: a point lies in an orbit closure exactly
when its entire double coset lies there. A boundary point belongs to a distinct
orbit. Refinement and antisymmetry of the linear order therefore place its
orbit strictly earlier, as recorded by
`boundary_doubleCoset_subset_strictInitial`.

`leviVanishingSubfunctor_antitone` uses the published membership criterion to
show that enlarging a vanishing set shrinks the vanishing subfunctor. Applying
it to the three containments of vanishing sets proves `pqSupportInclusions`.
`RepSubfunctor.inclusionOfLE` bundles any pointwise containment as a natural
same-vector inclusion; the functor maps commute definitionally with these
inclusions. Finally `pqSupportInclusionMaps` applies this construction to the
three inequalities.

The provenance is derived from the published definitions and elementary
topological-group facts. No Bruhat decomposition, finite enumeration,
subquotient comparison, or geometric-lemma theorem is assumed. The field
need only satisfy the hypotheses of the published vanishing subfunctors:
Field, TopologicalSpace and T2Space, with affine ambient structure morphism,
locally compact nonarchimedean ambient rational points, and one represented
parabolic triple. Q is an arbitrary group-scheme morphism. The second
parabolic decomposition, shared Levi embeddings, connected reductivity of G
and local-field hypotheses of the full source setting are unnecessary for
these inclusions.

## Retained obligations

This is an auxiliary construction for Task 5300. It proves the inclusion
component of `PQSupportGradedStatement`, without changing that statement or
its imports. It does not prove the subquotient comparisons, the full
geometric-lemma piece comparison, the identity identification, or
`PQRegularityLemmaStatement`.

The sole import is the unchanged
`Langlands.Representation.Intertwining.PQRegularity`.
