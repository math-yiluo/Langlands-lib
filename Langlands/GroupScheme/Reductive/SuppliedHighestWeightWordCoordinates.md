# Highest-weight word coordinates from supplied full simple-root data

This internal module derives full opposite-unipotent word coordinates and a
nonzero highest-weight endpoint from explicitly supplied linked simple-root
data. It does not construct the split pinning, coroot-span proof, or linked
simple-root family. These remain obligations of the independent Steinberg
big-cell construction; this conditional module is not the target theorem.

`SimpleRootCoordinateFamily` consists of one `LinkedRootParametrization` for
each simple root of a supplied pinning. Only that structure and its fields
are used, not its existing existence theorem or canonical choice. Each pair
contains two full intrinsic-root parametrizations, their opposite torus
characters, and the literal rank-one relation on every relative scheme test.
`suppliedSimpleLoweringMap` selects its negative map.

The full word chart transports the supplied negative parametrizations by
actual torus-normalizer conjugation using
`reflectionWordLoweringMaps_represents_of_fullSimpleMaps`. Distinct word
roots give distinct characters; a word listing the positive roots gives
exactly the negative roots contracted by minus the polarization of rho.
The generic ordered-product theorem for these full root functors then gives
injectivity and surjectivity on every relative scheme test. In particular,
these claims include nonaffine and nonreduced tests.

The endpoint proof applies the generic highest-weight reflection-word
coefficient theorem to the supplied positive and negative maps and their
rank-one relations. The simple coroot pairing of `m rho` is `m`. The resulting
coefficient is a nonzero scalar times the invertible rational word action
on a nonzero highest vector, hence is nonzero. Finally, the positive-root
word theorem chooses a word listing every positive root once, with the full
chart and the coefficient property for this same supplied family.

The combinatorial root enumeration, generic ordered-product argument and
generic highest-weight endpoint calculation are reused from the
Library. Fullness is transported from the supplied data; it is not inferred
from monicity and a root-dimension theorem. No root-map existence
proof, canonical linked-root choice, or canonical-rho Borel assembly
is used. This module adds no external source assertion.
