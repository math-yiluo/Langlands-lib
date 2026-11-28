# Extending a morphism from a dense open

`AgreesOn` compares two morphisms with open domains by testing scheme-valued
points in the intersection. `AgreesOn.of_dense` promotes agreement on an
open dense in a local piece to agreement on its entire intersection with the
given domain. The proof restricts the dense open to that intersection and
uses extensionality along a dominant morphism, with reduced source and
separated target.

In `exists_extension`, each local map agrees with the prescribed map on the
dense open. On overlaps the local maps consequently agree on a dense open
and hence everywhere. The open cover glues them and the resulting map
restricts to the original map. This is the open-cover construction used for
the two multiplication extensions in `Mul` and `MulBar`.
