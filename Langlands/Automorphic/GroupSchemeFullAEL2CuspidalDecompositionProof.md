# Discrete decomposition of the full cuspidal Hilbert space

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeFullAEL2CuspidalDecomposition`
proves `GroupSchemeFullAEL2CuspidalDecompositionStatement`. It assumes
compactness of the integrated right action for each compactly supported
continuous weight and its integrability witness.

Let `S` be the complete space of full almost-everywhere cuspidal `L²`
classes. The original bounded right action preserves inner products by
`fullAEL2CuspidalRightTranslate` and has continuous orbits by
`fullAEL2CuspidalOrbitMap`. Apply
`Langlands.Analysis.invariantSubspaceDiscreteDecomposition` to this action
with the ambient space `S` and invariant submodule `⊤`. The integrated
operator in the criterion is the original `fullAEL2CuspidalIntegratedAction`
precomposed with the continuous inclusion of `⊤`. Compactness follows
from the hypothesis by `IsCompactOperator.comp_clm`.

The criterion gives nonzero, closed, invariant, irreducible submodules
that are pairwise orthogonal and whose closed span is `S`. Each submodule
is complete by closedness. The proof reindexes the pairwise orthogonality
and the closed span over the subtype of members of the family, and then
uses `IsHilbertSum.mkInternal` for their inclusions. The criterion's
finite-multiplicity clause applies directly to the submodules related by
intertwining linear isometries for the cuspidal right action.

This specialization of the compact-operator criterion implements the
decomposition step of Getz–Hahn, *An Introduction to Automorphic
Representations* (2024), Lemma 9.3.1 and Corollary 9.3.2, printed p. 247
(PDF p. 259). The source is registered as
`getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
