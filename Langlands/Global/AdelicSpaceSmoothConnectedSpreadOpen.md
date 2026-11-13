# Smooth adelic openness for arbitrary supplied models

This derived supporting unit states and proves
`AdelicSpaceSpreadSmoothOpenOfLangWeilStatement`: the exact
`SpaceUniformLangWeilStatement` implies the unchanged published
`AdelicSpaceSpreadSmoothOpenStatement`. The conclusion covers both global-field
characteristics, every infinite number-field factor, arbitrary separated models
of finite type of the source and target, and their original adelic topologies.
The two supplied models may have different sets of inverted places. No constant
relative dimension is assumed.

The proof `adelicSpaceSpreadSmoothOpen_of_langWeil` first applies the published
smooth connected model construction to the actual generic-fibre arrow. This
gives separated finite-type models over one common ring of S-integers, a smooth
model arrow with nonempty geometrically connected fibres, generic-fibre
isomorphisms, and the commuting square with the original arrow. In the
function-field case the common set of inverted places is nonempty. The explicit
surjectivity hypothesis in the target statement is not needed separately,
because its geometric connected-fibre predicate already includes nonemptiness.

The full model adelic-openness theorem, with the exact Lang–Weil premise, makes
this model arrow open on its actual adelic points. The existing spread
homeomorphisms and their naturality transport openness across the commuting
square to the specified generic fibres. Finally, the published independence
conjunct of `adelicSpacePointTopology` identifies the common models' source and
target topologies with the two original supplied topologies, respectively.
Rewriting by these two equalities proves the required conclusion.

The provenance is internal: the smooth connected model descent, the full model
openness theorem, the spread transport lemma, and the published topology
independence theorem. This unit provides the remaining arbitrary-model assembly;
it does not prove the Lang–Weil estimate or the unconditional theorem. Its
conditional statement and proof retain that estimate explicitly.
