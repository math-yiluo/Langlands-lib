# Comparison of Hopf coordinates and actual Lie coordinates

This internal construction compares two existing choices of coordinate algebra
for an actual affine group scheme. It uses the published affine presentations
and point constructions; it attributes no new assertion to external literature.
The scalar ring is an arbitrary `CommRingCat R` in universe `u`, and the group
scheme `G` over `Spec R` has affine structure morphism.

`AffineCoordinates.lieCoordinateAlgEquiv` is an `R`-algebra equivalence from
`AffineCoordinates.hopfAlgebra G` to `Lie.coordinateAlgebra G`. The first algebra
comes from a chosen algebra cogroup presenting the group scheme, and the second
comes from the affine presentation used for its actual Lie kernels. These
choices need not coincide definitionally. The construction composes
`Lie.coordinateIso G` with the inverse of
`AffineCoordinates.coordinateSchemeIso G`, then applies full faithfulness of
relative spectrum and takes the resulting opposite algebra isomorphism.

`pointEquiv_lieCoordinateAlgEquiv` identifies the point defined by this
equivalence with `Lie.coordinateIso G`. The natural form
`pointEquiv_comp_lieCoordinateAlgEquiv` says that composing any algebra map out
of the Lie coordinate algebra with this equivalence gives the same actual
affine point under the two coordinate descriptions. Its test algebra is any
`CommAlgCat R` in universe `u`.

The lemmas `pointEquiv_hopf_counit` and `pointEquiv_hopf_mul` identify the Hopf
counit with the actual identity point and the Hopf comultiplication followed by
the product map of two algebra maps with multiplication of their actual
points. The Hopf operations are the cogroup operations by construction.
The relative spectrum functor preserves these operations, and the chosen
comparison is an isomorphism of group objects. These facts prove the two point
identities.

`coordinateOrigin_comp_lieCoordinateAlgEquiv` states that evaluation at the
actual group identity after the comparison is exactly the Hopf counit.
The proof applies injectivity of the affine point equivalence, uses its natural
comparison above, and identifies both sides with the identity point.
`lieCoordinateAlgEquiv_counit` is its value on each element.

For any field `k` in universe `u` and group scheme `H` over `k` with affine
structure morphism, `comul_comp_lieCoordinateAlgEquiv` states that tensoring the
comparison with itself carries the Hopf comultiplication to
`CharacterUnits.comul H` after the comparison. Here
`CharacterUnits.Coord H` is the existing `Lie.coordinateAlgebra H`. The proof
expresses the tensor map as the product map of the two tensor inclusions,
applies injectivity of the point equivalence, and uses the Hopf multiplication
identity and the natural coordinate comparison. Both resulting points are the
product of the two universal points defining `CharacterUnits.comul`.
`lieCoordinateAlgEquiv_comul` gives the pointwise formula with `k` as scalar
type.

The field restriction on these last two lemmas comes from the existing
`CharacterUnits` interface. No smoothness, connectedness, finiteness,
splitness, action, weight, or root assumption is used. This supporting
comparison does not assert the existence or structure of root subgroups.
