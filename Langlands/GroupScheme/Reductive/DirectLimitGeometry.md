# Reductive and connected fibre loci over a direct limit of rings

Worker 606.

`directedSystemBaseChange` constructs the actual base changes of a group over
one ring in a directed system to all later rings. The accompanying theorems
apply the published geometric loci to this family and its base change to a
specified ring colimit. No injectivity or Noetherian hypothesis is used.

`identityComponentReductiveLocus_eq_univ_iff_eventually` rewrites all loci as
preimages of the original group's locus using
`identityComponentReductiveLocus_baseChange`. Its openness is the published
`identityComponentReductiveLocusOpen`. The open-set eventual-fullness lemma
from `Langlands.AlgebraicGeometry.DirectLimitLocus` gives the equivalence.

`geometricallyConnected_baseChange_iff_eventually` uses constructibility of the
actual geometrically connected fibre locus for the original smooth affine
morphism. Smoothness supplies local finite presentation and affineness supplies
quasi-compactness and quasi-separatedness. The base is an affine spectrum, so
local constructibility is constructibility. The locus commutes with base
change and is full exactly when the morphism is geometrically connected.
Constructible-set eventual fullness then gives the claimed equivalence.

These are internal adapters derived from the imported Library results. They
implement the two geometric ingredients in Conrad, *Reductive group schemes*
(2014), Corollary 3.1.11, proof on p.89 (registered source
`conrad-2014-reductive-group-schemes`). They do not prove the full four-clause
target or the separate semisimple openness result.
