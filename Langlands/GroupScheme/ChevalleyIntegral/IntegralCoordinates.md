# Integral coordinate tori and the field-comparison adapter

This internal construction expresses the full-lattice torus of the fixed
generic Chevalley closure as the coordinate split torus over the base ring.
It uses the identity coordinates on the entire lattice of integer-valued
functions on the finite coordinate type. It retains central directions and
allows an empty coordinate type or root system.

The diagonalizable coordinate comparison is defined over every commutative
ring. Its canonical base-change square is proved on all test schemes:
both composites send a character-valued point to its values on the same
coordinate basis vectors. The inverse square follows by cancellation.

Precomposing the integral torus with the inverse coordinate comparison
gives an actual closed subgroup of the same fixed integral model.
Its base change is the inverse field-coordinate comparison followed by the
field torus of `FieldEmbedding`. The torus-compatibility theorem of that
module therefore identifies it with the supplied field group's coordinate
torus followed by its closed embedding in the fibre.

Consequently, if for every field algebra there is a supplied field Chevalley
group for which this closed embedding is an isomorphism, the inverse
isomorphisms satisfy `HasFieldComparisons` for the one integral model and
the one coordinate torus. This is an adapter to `ModelComparison`, not a
proof of its isomorphism hypothesis. The reverse field-fibre containment
and the unconditional integral-existence theorem remain open.
