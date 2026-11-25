# Refining the torus splitting cover

This internal construction refines the supplied relative torus's small étale
splitting cover. On each splitting chart, reductivity, closed torus inclusion,
fibrewise maximality, the relative Borel predicate and the all-test torus
containment pull back. The split-torus dynamic Borel neighbourhood cover is
therefore available on that chart.

`RelativeBorelDynamicPresentation.cover` binds these chart covers to the
original splitting cover. Both levels are indexed in the scheme universe.
Composition of étale covers makes the result a small jointly surjective étale
cover of the original arbitrary base.

`coverOfNeighbourhoods` performs the same cover binding for an explicitly
supplied family of neighbourhood data. Keeping that family as an argument
permits the final local-presentation proof to refer directly to each
neighbourhood projection without unfolding its geometric construction.

This file constructs covering families. The canonical transport of the dynamic
Borel data from their iterated pullbacks to the direct original-group pullbacks
is supplied by `BorelDynamicCompositePresentation`; the full local-presentation
proposition is proved in `BorelDynamicPresentationProof`.
