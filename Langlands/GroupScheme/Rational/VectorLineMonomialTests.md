# Monomial coordinates on every scheme test

The definition `RelativeRoot.monomialMap` constructs an actual morphism of
schemes over the field from a scalar and a natural-number exponent, using the
inverse of the target coordinates at the universal source point. Naturality of
both coordinate systems proves its monomial formula on every scheme test. The
map need not preserve the group operation for arbitrary exponents.

The internal derived transfer lemma extends a monomial coordinate identity from all
coefficient algebras to arbitrary schemes over the original field. Its input is
an actual map between group schemes with supplied natural one-dimensional
vector coordinates. Its affine hypothesis concerns every coefficient algebra,
including nonreduced ones, rather than only field points.

The proof expresses the source group scheme as an affine spectrum using its
natural vector coordinates. It transfers the affine formula to the universal
point by the affine comparison isomorphism and naturality. Pulling back this
universal equality along any point gives the claimed formula on its test scheme.
The coefficient is explicitly the pullback of the original field scalar along
the test scheme's structure morphism. No affineness or reducedness assumption is
placed on that test scheme, and the scalar and exponent are fixed in advance.

The standard additive-group corollary expresses the conclusion as equality
between actual `VectorGroup.scalarPoint` morphisms. Coordinate extensionality
converts the general line-coordinate identity to that point formula.

This is an internal consequence of the published vector-coordinate and affine
scheme interfaces. It makes no existence claim about the monomial polynomial,
its coefficient, or its degree.
