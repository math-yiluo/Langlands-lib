# Root lattice comparisons for uniform parabolic faces

This internal construction transports the integral indexing data of standard
parabolics between groups over two potentially unrelated fields. It is derived
from the Library definitions of relative roots, generic cocharacters, positive
and simple relative roots, and standard cocharacters.

`ParabolicRootLatticeComparison` consists of additive equivalences of both full
integral lattices, preservation of the actual relative-root sets, and preservation
of the character/cocharacter pairing. It is supplied comparison data, not a claim
that all groups admit such comparisons.

`generic_iff` and `positive_iff` follow from the root and pairing identities.
`simple_iff` also uses additivity and surjectivity to transport decompositions
into two positive roots in both directions. `faceEquiv` therefore bijects all
subsets of the simple roots. `standard_iff` transports the zero and positive
pairing conditions defining a standard cocharacter for any such face. All maps
retain the full character and cocharacter lattices, including central directions.
