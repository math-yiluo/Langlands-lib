# Dimension of actual closed stalk support

`supportDimension M` is the topological Krull dimension of
`closedStalkSupport M`, viewed as a subspace of the scheme. Its value lies
in `WithBot ℕ∞`; in particular the empty support has dimension bottom.
The previously defined predicate `HasSupportDimensionLT M e` is equivalent
to `supportDimension M < e` for each natural number `e`. Isomorphic
modules have the same dimension because they have the same closed support.

For a scheme morphism whose underlying map is a closed embedding,
`coe_closedStalkSupport_pushforward` identifies the closed support of its
actual pushforward with the image of its original closed support. The
actual-stalk image formula and the fact that closure commutes with a
closed embedding prove this equality. The closed embedding restricts to
a homeomorphism from the original closed support to that image, so their
topological dimensions agree. Thus every `HasSupportDimensionLT` bound
is both preserved and reflected. No coherence or condition on the
morphism's stalk-ring maps is assumed.

For a short exact sequence, the middle module satisfies a given strict
support bound exactly when both outer modules do. Their closed supports
form a binary union. Every irreducible closed subset of this union lies
in one of the two closed supports. Applying the bound there proves the
reverse implication; containment of each outer support in the union
proves the forward implication. This holds also for bound zero.

`stalkSupport_structureModule` proves that the actual structure module
has a nonzero abelian stalk at every point. If its germs of one and zero
were equal, the presheaf germ comparison would make their restrictions
equal on some neighborhood. Those restrictions are one and zero in the
section ring. Mapping into the nonzero local ring at the point gives a
contradiction. Taking closure gives full closed support, and the
homeomorphism from the whole-space subspace to the scheme identifies its
support dimension with the scheme's dimension.

Restriction to an open preserves the stalk support at the points of that
open, by the canonical restriction-stalk isomorphism. On an irreducible
scheme, a module isomorphic to the structure module on a nonempty open
therefore has full closed support: the open is contained in its stalk
support and is dense. Finally tensoring with a line bundle preserves
closed support and support dimension, by the existing equality of actual
stalk supports under such tensoring.

These are internal support comparisons in arbitrary universe `u`, using
the published actual module, closed-support, and topological-dimension
constructions. They do not require Noetherianness or assert an
Euler-polynomial or positivity theorem.
