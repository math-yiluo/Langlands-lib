# Explicit fiber-relation coequalizers of continuous actions

This internal construction takes an equivariant morphism `q : X ⟶ Y` of
jointly continuous actions on topological spaces. The group parameter is
actually allowed to be a topological monoid; its universe is independent of
the universe of the spaces. No separation, nonemptiness or openness condition
is imposed.

`Relation q` is the actual subtype of `X × X` consisting of pairs with equal
image under `q`. It inherits the product subspace topology.
`relationMap`, `relationAction` and `relation` apply the original action in
both coordinates. Equivariance of `q` proves that each map preserves the
subspace. The monoid laws follow from those on `X`. Joint continuity follows
by composing the original joint action with each coordinate projection and
then lifting the resulting continuous product map to the subtype.

`fst` and `snd` are the two continuous equivariant projections.
`pair` constructs the unique continuous equivariant map to the relation from
two maps with equal composites. Its two projection identities and pointwise
uniqueness construct `isLimit` for `pullbackCone`: this is the categorical
kernel pair, proved from the actual product subspace.
`condition` and `cofork` retain `q` as their cofork leg.
`condition_iff_factorsThrough` identifies the categorical equality of the
two composites with constancy on every fiber, including pairs of distinct
source points in a single fiber.

When the underlying map of `q` is quotient, `liftMap` uses Mathlib's
`IsQuotientMap.lift` on the underlying continuous map of a morphism equalizing
the two projections. Its triangle is `liftMap_apply`. Surjectivity of `q`
reduces the equivariance equation for the descended map to that triangle and
the equivariance equations for the two original maps. This constructs
`desc`. The theorem `fac` gives the exact factorization and `desc_unique`
uses the same surjectivity to prove uniqueness. `isColimit` packages these
constructions with `Cofork.IsColimit.mk`.

The provenance is internal: this is the explicit continuous equivariant
version of the quotient-map universal property, derived from the original
action laws and Mathlib's proved continuous quotient lift. It assumes
neither the descended equivariant morphism nor the categorical colimit.
It is a topological categorical construction and makes no claim about
algebras, analytic maps or sheaf descent.
