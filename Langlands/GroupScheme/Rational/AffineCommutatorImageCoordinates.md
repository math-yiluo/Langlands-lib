# Coordinate injectivity of the actual affine commutator image

This internal adapter relates the chosen coordinates of actual pointed affine
schemes to the explicit range algebra used to construct the closed commutator
image. The geometric motivation is the equivariant coordinate inclusion in
Conrad–Gabber–Prasad, *Pseudo-reductive Groups*, second edition (2015), Lemma
3.3.4, printed pp.108–109 / PDF pp.134–135. The present argument is an affine
coordinate calculation and uses no smoothness, reducedness or split-torus
assumption.

Over any field in an arbitrary universe, take affine group schemes `G`, `H`,
`K` and group homomorphisms `i : H ⟶ G`, `j : K ⟶ G`. The earlier image module
defines the actual range subalgebra of the commutator pullback in the independent
tensor coordinates, its spectrum `imageScheme`, and the actual morphism
`imageFactor : H.X ⊗ K.X ⟶ imageScheme i j`.

`imageCoordinates` is an algebra equivalence from the chosen pointed-scheme
coordinates of the image to this explicit range algebra. `inputCoordinates`
identifies the chosen product coordinates with the tensor coordinates used in
that construction. Both equivalences are obtained from their actual affine
scheme presentations by full faithfulness of the affine spectrum functor.

`imageFactor_pullback_coordinates` says that conjugating the actual coordinate
pullback by these equivalences gives precisely `Subalgebra.val`, the inclusion of
the range algebra. The proof evaluates the pullback on the tensor presentation
and uses affine point-coordinate naturality. `imageFactor_pullback_injective`
then follows from injectivity of this subalgebra inclusion and of the image
coordinate equivalence.

This unit establishes the concrete injectivity needed for later equivariant
support transport. It does not assert a weight decomposition, a commutator
weight bound or a generated-subgroup theorem.

The affine-product instance follows the base-change construction also used by
Worker 1228 in the product-coordinate development. The product coordinates here
are specialized to the existing commutator presentation; no product action or
tensor weight-space interface is introduced.
