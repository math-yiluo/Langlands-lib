# Finite generation and smooth coproducts

This internal module proves that the actual integer-module Hom functor of a
smooth complex representation finitely generated over its actual group
algebra preserves coproducts. It also proves the corresponding result in
any full smooth subcategory closed under the actual direct sums in
question. Group and index universes are independent; carriers have universe
`max uI uV`, so the direct sums remain in the same smooth category.

The argument uses the published `SmoothCoproducts` construction, with its
algebraic finite-support carrier and componentwise smooth action. It does
not require an abelian-category structure on the full subcategory.

Choose finitely many group-algebra generators of the source. The union of the
supports of their images is finite. Every coordinate morphism outside this
union vanishes on the generators, hence vanishes as a group-algebra linear
map. Equality into the direct sum is tested by its coordinate projections.
The inclusion/projection identities therefore express each morphism as the
finite sum of its nonzero components.

`homDirectSumIsColimit` applies the companion
`homCofanIsColimitOfFiniteDecomposition` to obtain a coproduct of actual
integer Hom modules. The actual restricted integer actions are the ones
in `preadditiveCoyonedaInt`; the companion construction checks linearity
using additivity and the uniqueness of integer scalar multiplication.
The ambient direct-sum colimit then proves preservation of the discrete
family by that functor.

For an object property `Q`, `fullSubcategoryDirectSumCofan` bundles the
same actual direct sum when it satisfies `Q`. Fullness restricts the
ambient universal property to give
`fullSubcategoryDirectSumIsColimit`. The component projections likewise
belong to the full subcategory. Finite decompositions lift from the
ambient smooth category because the inclusion functor is faithful and
additive. `homFullSubcategoryDirectSumIsColimit` constructs the colimit
of the actual integer Hom cofan there.

`hom_preservesFullSubcategoryCoproducts` assumes membership of every
`I`-indexed actual direct sum of objects of `Q`. The membership condition
is quantified over the decidable-equality instance used by the concrete
construction. The conclusion has no decidable-equality premise: classical
choice supplies that instance internally. Preservation for every
`Discrete.functor` family gives preservation for all diagrams of shape
`Discrete I`.

The internal provenance is the finite-generator support argument and
restriction of an existing universal property, combined with the
preadditive finite-decomposition helper. The finite-generation and
closure hypotheses remain explicit. This focused module proves neither
finite generation of a norm-kernel restriction nor closure of an inertia
block; those inputs are required separately for the small-progenerator
application.
