# Cyclic coordinates on a given product of fields

`exists_cyclicProductFieldCoordinates` starts with a cyclic algebra and an
algebra isomorphism to a finite product of fields. It chooses one of the
given field factors and an isomorphism to a product of copies of that
factor. The zeroth projection agrees with the original projection to the
chosen factor. The cyclic generator shifts the nonfinal coordinates and
acts by a cyclic automorphism of the field at the wraparound. The total
degree is the number of product coordinates times the field degree.

The proof starts from the residue-field coordinates of
`CyclicAlgebraStructure.exists_coordinates`. The quotient map to the
chosen residue field is a surjective algebra map from the given product
to a field. The coordinate idempotents add to one, so at least one has
nonzero image. Its image is one by idempotence. Multiplication by it
shows that the quotient map depends only on that coordinate. The resulting
field map is injective and surjective, which identifies the residue field
with the corresponding field from the given product.

Transporting the residue-field coordinates by this isomorphism gives
the claimed zeroth projection and shift laws. The isomorphism preserves
the field degree and the fixed algebra, and its induced group isomorphism
on automorphisms preserves order. This proves cyclicity of the field twist.
The construction is an internal form of the cyclic product presentation
of Henniart–Lemaire, I.2.1, printed pp. 10–11 (PDF pp. 18–19).
