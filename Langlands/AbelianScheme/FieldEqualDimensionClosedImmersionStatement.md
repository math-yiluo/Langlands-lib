# Closed immersions in equal relative dimension

`Langlands.AbelianScheme.FieldEqualDimensionClosedImmersionStatement.{u}`
asserts that an actual homomorphism between two actual abelian schemes over
`Spec K`, with closed-immersion underlying scheme map, is an isomorphism of
underlying schemes when both abelian schemes are smooth of the same specified
relative dimension `g`. The field `K : Type u` and natural number `g` are
arbitrary. There is no algebraic-closedness or characteristic restriction.

`HasRelativeDimension` is the existing abbreviation for Mathlib's
`SmoothOfRelativeDimension`, and `hom f` is the existing underlying scheme
map of the actual homomorphism. The conclusion concerns this scheme map.
The statement does not separately construct an inverse in the abelian-scheme
category.

This is an internal geometric consequence of the published dimension and
integrality results. Smooth geometric connectedness makes the target integral.
The image of the closed immersion is homeomorphic to the source. A closed
point of the source has stalk dimension `g`, so the image has topological
Krull dimension at least `g`. The compact smooth target has dimension at most
`g`. A proper closed subset of an irreducible space has dimension plus one at
most the ambient dimension. These inequalities force the image to be the
whole target. A surjective closed immersion into a reduced scheme is an
isomorphism.

This file defines a proposition. Its proof requires a separate contribution.
It supplies a geometric step for the torsion-closure argument only after
equality of relative dimensions is proved. It asserts no torsion cardinality,
dimension equality for that closure, or torsion density.
