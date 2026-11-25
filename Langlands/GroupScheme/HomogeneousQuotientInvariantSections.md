# Global sections of a supplied homogeneous quotient

This internal construction identifies functions on an actual supplied
homogeneous quotient with right-invariant functions on its ambient group.
It applies to any base scheme `S` and any morphism `i : H → G` of group
schemes for which a
`HomogeneousQuotientFromEmbedding.HomogeneousQuotient i` is supplied.
No affineness, reductivity, field or normality hypothesis is imposed.

`IsRightInvariant i s` says that, on every relative scheme `T`, the pullback
of `s` along `g * i(h)` equals its pullback along `g`. Both arbitrary
nonaffine and nonreduced tests are included. These functions form
`rightInvariantSubring i`. The predicate is equivalent to equality of
pullbacks along the actual source and target maps of the coset-arrow
scheme `G ×_S H`.

For the supplied quotient `Q`, `right_mul_projection` follows directly
from its exact coset-fibre criterion. Hence pullback along `Q.projection`
defines a ring homomorphism `pullbackInvariantSections` into that
subring. In the reverse direction, if two relative points have equal
projection, their difference is the image of an actual subgroup point.
Right invariance therefore makes their pullbacks of the function equal.
The proof equips an arbitrary underlying scheme with the common
structure map to `S`, so this equality holds for every underlying scheme
test required by effective epimorphism descent.

The projection is smooth, surjective and quasi-compact, so Mathlib's fpqc
site supplies its effective epimorphism instance. The published
`UnitCocycleDescent.exists_appTop_eq_of_effectiveEpi` descends the function.
Injectivity follows from epimorphism detection of functions.
`invariantSectionsEquiv` is the resulting ring equivalence, with its
forward and inverse pullback formulas proved explicitly.

The provenance is the published homogeneous-quotient definition, its
actual coset relation, and the published effective-epimorphism function
descent theorem. This is a derived interface for a later affineness
argument; it asserts neither geometric reductivity nor affineness of `Q`.
The original quotient and its projection are retained throughout.
