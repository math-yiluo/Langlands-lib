# Exact root-depth kernels and ordinary facet roots

This internal supporting unit works in arbitrary universe `u` for a supplied
nonarchimedean local field, parahoric building data, and an integral model with
the specified unramified zero-subgroup and translated-subset fixer
characterization. The integral torus is closed and split, and the supplied
special-fibre quotient is an actual reductive quotient.

All three constructions explicitly assume `IntegralOppositeFactorsStatement`.
They do not prove that statement. The affine functional has the specified
generic root as derivative and vanishes everywhere on the apartment subset.

For a point in its whole depth group but outside strict depth,
`reflectionFunctional_eq_of_mem_diff` identifies its actual valuation functional
with the supplied functional. V5 places both actual opposite factors in the
negative depth group. Since the negative functional also vanishes on the
subset, the descended-model integrality theorem makes both factors integral
after conjugation. The opposite-factor statement then proves that the original
conjugated point is outside the actual radical preimage. This first implication
uses neither injectivity of the building comparison nor the root-reflection
axiom.

`quotient_reduction_eq_one_iff_mem_strictDepth` additionally assumes an injective
equivariant building comparison, the root-reflection axiom, and a nonempty
apartment subset. For an integral section in the conjugated whole depth group,
its actual quotient reduction is the identity exactly when its generic point
belongs to the conjugated strict-depth group. The forward implication uses the
preceding radical exclusion and the equality between the reduction kernel and
the actual radical preimage. The reverse implication uses
`StrictDepthFacetKernel` at any point of the subset.

`facetOrdinaryRootOfQuotientExclusion` certifies the original functional as an
ordinary affine root if one such integral section has quotient reduction
outside the doubled specialized root functor. Whole-depth integrality follows
from vanishing on the subset. The strict-depth kernel implication supplies the
other premise of `MappedOrdinaryRootQuotientCertificate`. The coercion theorem
states that the resulting ordinary root is exactly the original functional.

The provenance is an internal composition of the named valuation, model
integrality, opposite-factor, and quotient-kernel interfaces. The module does
not require that the subset be a facet, does not assert existence of the
outside point, and does not establish exact quotient-root comparison or the
host derivative root-datum theorem.
