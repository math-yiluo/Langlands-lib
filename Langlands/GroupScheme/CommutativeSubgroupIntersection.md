# Scheme-theoretic intersections inside a commutative subgroup

This internal construction equips the existing scheme-theoretic pullback
`subgroupIntersection f r` with commutativity when the source of `f` is a
commutative group scheme and the underlying map of `r` over the base is a
monomorphism. It works over any base scheme and uses the existing group law
on that pullback. It does not require a field, smoothness, or reductivity.

The first projection is a monomorphism by the pullback property. The published
categorical lemma
`Langlands.CategoryTheory.GroupObjectDescent.commMonObjOfMono` therefore
descends commutativity from the source of `f`. The definition
`commutativeSubgroupIntersection` has exactly the existing pullback as its
underlying group scheme. Its two actual homomorphisms have equal composites
in the ambient group, and the range of that composite equals the intersection
of the two original ranges on every test scheme. These equations are inherited
from `Langlands.GroupScheme.SubgroupIntersection`, without passing to geometric
or rational points.

The first projection is a closed subgroup whenever `r` is closed; the second
is closed whenever `f` is closed. These facts follow by pulling back the
corresponding closed immersion. When both input maps are closed, their
intersection functor is represented by the same composite. A compatible
pair of group maps lifts canonically to the intersection, and its two
projection equations and uniqueness follow from the pullback universal
property.

This is derived categorical infrastructure for the radical intersection
in `Langlands.GroupScheme.ParabolicRadicalTorusLeviStatement`. It asserts
no existence of a radical and no smoothness, connectedness, torus property,
maximality, or Levi property of this intersection. Those are separate
geometric obligations.
