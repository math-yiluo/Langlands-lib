# Positive roots and the actual dynamic tangent dimension

This internal, derived helper supplies the linear algebra step needed in
positive-root uniqueness. It applies over every field to an affine group
scheme locally of finite type, with a homomorphism from a split torus.
It requires neither reductivity nor maximality of that torus.

`RelativeRoot.weightSpace_le_tangentSubmodule_unipotent` puts an adjoint
character weight space with strictly positive pairing into the actual tangent
submodule of `Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)`. Its proof
uses the published exact equality
`RelativeRoot.tangentSubmodule_unipotent_eq_semigroupWeightSpan` and the
identification of conjugation action weights with adjoint weights.

`RelativeRoot.positiveWeightTangentInclusion` is the corresponding canonical
linear map from the positive weight space to the actual tangent submodule.
It is the submodule inclusion supplied by the preceding containment.

`RelativeRoot.two_le_finrank_tangentSubmodule_unipotent_of_distinct_positive_roots`
shows that two distinct positive roots force this tangent submodule to have
dimension at least two. Each root has a nonzero weight space by the definition
of `roots`. The internal split-torus weight decomposition makes distinct
weight spaces disjoint. Finite dimensionality of the actual Lie kernel and
the dimension formula for a sum of submodules then give the lower bound.

`RelativeRoot.positive_roots_eq_of_tangentSubmodule_unipotent_finrank_le_one`
deduces equality of positive roots from an explicit upper bound of one on
that same tangent submodule.

The provenance is internal: these are consequences of published actual-weight
and dynamic-Lie results and ordinary finite-dimensional linear algebra. This
module does not prove that the upper bound holds in semisimple rank one and
does not prove `RankOnePositiveRootUniquenessStatement`. That geometric
dimension bound remains a separate obligation.
