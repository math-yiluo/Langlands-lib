# Normalized affine points of direct pullbacks

This internal categorical coherence module compares points of the direct pullback
of an affine pinned model to the actual points of its scalar extension. The
intermediate scheme `W` is arbitrary. An affine coefficient test `Spec B → W`
comes with the stated equality of its composite base map with the algebra map
`Spec B → Spec A`.

`normalizedBasePointsEquiv` and `normalizedTestPointsEquiv` are multiplicative
equivalences. They first apply the canonical base-change composition isomorphism,
then the point adjunction for the remaining pullback. The formulas ending in
`_left` identify their underlying scheme maps. `NormalizedPointProjectionCriterion`
is the universally quantified affine-test projection formula, proved by
`normalizedPointProjectionCriterion`.

The remaining lemmas prove compatibility with constant sections, actual pinning
vectors and pulled comparisons. The pinning lemma assumes the displayed original
algebra structure on `B` and its scalar-tower compatibility. It uses
`scalarExtension_pinning_map_point` to identify the coefficient extension of the
chosen scalar pinning vector with the original model's dual-number root-vector
point. The comparison lemma follows from the two pullback projections and the
definition of `pullComparison`.

The provenance is internal: these are coherence identities for existing
base-change constructions, with no additional assertion from original literature.
The module supplies tools for an fppf torus correction; it does not assert that
such a correction already exists.
