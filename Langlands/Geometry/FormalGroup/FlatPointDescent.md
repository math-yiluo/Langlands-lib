# Descent of formal points along faithfully flat algebra maps

This internal infrastructure, implemented by Worker 921, proves
effective descent of actual formal-module points over coefficient
algebras. O and R are arbitrary commutative rings with an O-algebra
structure on R and possibly different universes. The coordinate set
is finite; test algebras have the universe of R.

An injective coefficient ring map is injective on points, as can be
checked on their constant coordinates. A nilpotent point whose
coordinates lie in the image of such a map comes from a point over
the source: choose coordinate preimages and descend their nilpotence
by injectivity.

The file constructs the actual tensor pushout of two maps of
coefficient algebras, with its two structural maps and their
commutativity relation. A faithfully flat input leg makes the
opposite pushout leg faithfully flat by tensor base change.

`exists_algebraMapPoints_eq` assumes a faithfully flat algebra map
from A to B and an actual point over B whose images agree under
every pair of maps from B equalized by A. In particular its two
pullbacks to B tensor B over A agree. The faithfully flat algebra
equalizer theorem puts each coordinate in the image of A. Coordinate
descent therefore produces the actual point over A.
`existsUnique_algebraMapPoints_eq` adds uniqueness using injectivity
of faithfully flat point restriction.

No finite-presentation condition is needed for this descent theorem.
These are internal inputs to the actual factorization and inverse
construction, not quotations from external literature.
