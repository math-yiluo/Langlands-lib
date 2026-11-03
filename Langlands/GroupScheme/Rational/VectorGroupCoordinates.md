# Actual vector-group isomorphisms from natural coordinates

Natural group coordinates on every scheme test produce an actual
group-scheme isomorphism to the standard polynomial vector group of the
same dimension. The construction composes the given coordinates with the
inverse standard coordinates and applies the Library's `isoOfPoints`.
The coordinate formula for the resulting morphism holds on every test,
including nonreduced tests.

Consequently `IsVectorGroupOfDimension V n` is equivalent to the existence
of an actual isomorphism from `V` to `VectorGroup.groupScheme k n`. This
comparison requires no prior affineness or smoothness assumption. The
isomorphism also proves that `V` is affine, smooth and connected. The
standard model is the spectrum of the polynomial ring in `n` variables;
polynomial smoothness and the fact that this ring over a field is a domain
give these geometric properties.

The dimension in natural vector coordinates is unique. Each coordinate
system induces linear coordinates on the actual dual-number Lie kernel,
as implemented by `vectorLieCoordinates`. Composing those linear
equivalences identifies the coordinate vector spaces over the ground
field. Their equal finite ranks give equality of the two dimensions.
The zero-dimensional case is included.

This is an internal consequence of the existing natural-point
isomorphism, polynomial vector-group, smoothness and Lie-coordinate
constructions. It supplies the scheme comparison and fixed-dimension
facts needed by structural vector-group targets. It proves no
stable-central-subgroup existence or torus-action linearization theorem.
