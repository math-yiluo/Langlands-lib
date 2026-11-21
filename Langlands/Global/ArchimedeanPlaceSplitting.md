# Smooth splitting at one archimedean place

For a number field and a matrix size, a chosen real or complex place gives
an actual local subgroup of the invertible matrices over the mixed
archimedean space. Projecting each matrix entry to the chosen place gives
a group homomorphism on units. The complementary factor of a group element
is obtained by dividing out its projected local matrix along the inclusion.
It has identity at the chosen place and the original coordinates elsewhere.
It commutes with the local subgroup, and multiplying it by the included
projection recovers the original element.

`PlaceSplittingStatement` records the two smoothness claims and the product
and commutation identities for each real and complex place. Smoothness of
the projection follows from its real linear matrix map and the open unit
charts. The complementary factor is smooth by the existing smooth place
inclusion, multiplication, and inversion. Commutation is checked by applying
all the real and complex projections, which jointly determine a unit.

This internal result uses the Library's mixed-space algebra projections
and actual place inclusions. It supplies the group splitting needed to
compare local and global smooth vectors.
