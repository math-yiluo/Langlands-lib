# Testing membership in open subfunctors on scheme points

This internal helper concerns an arbitrary presheaf on schemes over a fixed
base and a subfunctor whose inclusion is a representable open immersion.
There is no sheaf, group, finiteness or separation hypothesis on the presheaf.
The assertions are derived from the imported Library and Mathlib
constructions; no separate literature assertion is introduced.

`mem_app_iff_range_subset` represents the inverse image of the open subfunctor
on a test scheme. It identifies membership after a map of test schemes with
containment of the map's topological range in the represented open. The
pullback range formula identifies the inverse-image subfunctor, and the
universal property of a scheme open immersion identifies its sections with
maps whose range lies in that open. `mem_map_iff_range_subset` expresses the
same criterion for a section of the ambient presheaf.

`mem_of_jointly_surjective` uses this criterion to descend membership along
any family of scheme maps whose topological ranges cover the test scheme.
The index type may have any universe. `mem_of_surjective` specializes to
one surjective morphism, and `mem_iff_of_surjective` includes the converse,
which is the subfunctor's stability under restriction. No flatness or local
finite presentation assumption is needed.

`residueFieldTest` and `residueFieldPoint` express the canonical point
Spec of the residue field at a point of a test scheme as an object and
morphism over the fixed base. Their ranges cover the test scheme, one point
at a time. Consequently `mem_iff_residueField` states that membership in the
open subfunctor can be checked after restriction to every such field point.
This supports the later passage from comparisons at field-valued points to
invariance of an open subfunctor on all test schemes.

`mem_of_field_tests` allows checking all field-valued points instead of naming
the residue-field points explicitly. `eq_of_field_tests` identifies two open
subfunctors when they agree on all such field tests over the base.
`invariant_of_field_tests` applies the same argument to a natural
transformation: if two sections with the same image have equivalent membership
on every field-valued test scheme, they have equivalent membership on every
scheme. Naturality ensures that their restrictions still have the same image.
These statements impose no restriction on the fields, including their
characteristic, perfectness or relation to the base.
