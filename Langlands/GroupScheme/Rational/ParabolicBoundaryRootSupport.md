# A proper simple-root index from a nonstrict nonnegative exponent

This is derived internal support for the converse direction of Renard VII.2.4.
It retains a compatible presentation of the original actual parabolic, Levi
and split component over a field of arbitrary universe. Ambient affineness
and local finite type are explicit. It makes no root-independence or
relative-root-system assumption.

The existing finite-family cone comparison expands a vector of the
nonnegative cone on the original complementary simple roots, even if two
roots have the same restriction to the split component.
`nonnegRootCoefficients` selects such an expansion.
`boundaryRootIndex` is the old selected-root index enlarged by the simple
roots with positive coefficient. It contains the old index and is contained
in the original simple-root set. If the vector misses the strict cone, this
enlarged index is proper: otherwise the same expansion has positive
coefficients on every complementary simple root and gives strict-cone
membership. An explicit omitted complementary simple root has coefficient
zero. No uniqueness of the chosen coefficients is claimed.

The restriction theorem applies to an actual map between split tori.
If its composite into the presentation torus kills every character in the
constructed index, restriction sends the vector to zero. The proof maps
the finite expansion term by term: zero coefficients contribute zero, and
positive coefficients have their root in the constructed index.

For nested actual parabolics, the final theorem uses the previously
constructed factor of the larger Levi's split component into the original
fine torus. If the constructed index lies in that Levi's simple-root face,
the exact root comparison puts every positive-support root in the actual
larger Levi's relative-root set. Its roots vanish on its central split
component, so the original vector has zero restriction to that component.
All-test nesting, the common-Levi composite equality, both supplied root
presentations, connected reductivity and the displayed affine/finite-type
instances are retained.

This module constructs the index and proves the restriction conclusion for
supplied compatible nested geometry. It does not construct a larger
parabolic realizing that index, prove it proper as an actual subgroup, or
project a normalized Jacquet exponent to an outer exponent. Those remain
necessary steps for the converse unitary-vanishing argument. No form of
Casselman's analytic criterion or the full VII.2.4 equivalence is asserted.
