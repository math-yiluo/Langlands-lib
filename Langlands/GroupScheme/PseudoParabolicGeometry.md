# Smooth affine product presentations of pseudo-parabolic subgroups

This derived internal module constructs a smooth affine product presentation of
the actual source `P` of a supplied pseudo-parabolic inclusion `i : P → G`, and
proves that `P` is smooth, affine and locally of finite type over the field.
Every declaration works over an arbitrary field `k : Type u`. The connectedness
conclusion of `PseudoParabolicSubgroupStructureStatement` remains a separate
obligation.

`SmoothAffineProductPresentation P` records two group schemes over `Spec k`,
smoothness and affineness of their structure maps, and a relative scheme
morphism from their ordered product to `P`. The recorded morphism is both a
categorical epimorphism of underlying schemes and surjective on scheme points.
It is not required to be a group homomorphism or flat.

`IsPseudoParabolicSubgroup.smoothAffineProductPresentation` chooses such data
from the existing pseudo-parabolic predicate. Its construction proceeds as
follows:

1. Unpack the supplied ground-field unipotent radical `j : U → G`,
   cocharacter `χ`, and represented all-test fppf product witness.
2. Use `Dynamic.Affine.parabolicScheme χ` and
   `Dynamic.Affine.parabolicHom χ` to represent `Dynamic.parabolic χ`.
   The published theorem `dynamicSmooth` proves that this group scheme is
   smooth. Smoothness of `U` is already part of `IsUnipotentRadical j`.
3. Both inclusions are closed immersions into affine `G`. Composing their
   structure maps therefore proves that both factors are affine over `k`.
   Closedness also supplies the monicity needed to represent the radical's
   range by the given `j`.
4. Apply the published `SubgroupFunctor.IsFppfProduct.productMul` construction
   to these two representatives. Its `epi_productMul` and
   `surjective_productMul` theorems supply the two image properties.

The construction first proves that these presentation data are nonempty and
then uses classical choice. It retains the given target `P`; the definition of
`IsPseudoParabolicSubgroup` and its fppf-local product are unchanged. The
radical is the supplied ground-field radical.

The smoothness argument has two general steps.
`smooth_of_affine_epi` applies to a group scheme locally of finite type over
`k` whose underlying scheme is affine, with an epimorphism from an affine
scheme geometrically reduced over `k`. The imported
`SchemeImageGeometry.geometricallyReduced_of_epi` descends geometric
reducedness to the group. Installing its actual group-object structure permits
Mathlib's `AlgebraicGeometry.smooth_of_grpObj` to conclude smoothness.

`smooth_of_product_epi` specializes this argument to the product of two smooth
affine groups. Smoothness and affineness of the product structure map follow
from pullback stability and composition. The published
`Langlands.AlgebraicGeometry.smoothGeometricallyReduced` supplies geometric
reducedness of that smooth structure map, which is also the composite through
the relative product morphism. The preceding descent lemma then applies.
`SmoothAffineProductPresentation.smooth` uses this specialization for its
recorded factors and morphism.

Finally, `IsPseudoParabolicSubgroup.source_isAffineHom` and
`source_locallyOfFiniteType` follow by composing the closed inclusion
`i` with the ambient structure map. Ambient smoothness supplies local finite
type. Installing these two properties and using the chosen presentation's
`smooth` theorem proves `IsPseudoParabolicSubgroup.source_smooth`.

The provenance is the stated composition of existing proved Library results
and Mathlib scheme geometry. This module introduces no new literature
translation and claims no connectedness result for `P`.
