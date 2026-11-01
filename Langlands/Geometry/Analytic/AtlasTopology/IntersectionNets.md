# Intersecting two nets on the same topological space

This module constructs the binary intersection operation on nets of subsets of
an arbitrary topological space. The family is the existing
`intersectionFamily τ υ`: its members are the actual subsets `U ∩ V` with
`U ∈ τ` and `V ∈ υ`. No compactness, separation or openness hypothesis is used.

`IsQuasinet.intersectionFamily` proves that this family is a quasinet when
both inputs are quasinets. At a point, take the finite neighborhood witnesses
from both inputs. The image of their finite Cartesian product under set
intersection is finite, consists of members of the intersection family, and
every one of its sets contains the point. Its union equals the intersection
of the two original witness unions, and hence is a neighborhood.

`IsNet.intersectionFamily` proves the full net condition. For two new members
`U ∩ V` and `U' ∩ V'`, the original net conditions give finite relative local
refinements of `U ∩ U'` by members of `τ` and of `V ∩ V'` by members of `υ`.
The existing `LocallyRefines.intersectionFamily` intersects those finite
relative witnesses. Reordering the four set intersections gives a local
refinement of `(U ∩ V) ∩ (U' ∩ V')` by members of the new family.
`isQuasinet_restrictedFamily_iff` translates it into the required quasinet
on the actual induced subspace.

`intersectionNet` takes two families equipped with net proofs and returns
their intersection family equipped with the constructed proof.
`intersectionNet_val` records its underlying family by definitional equality.
The construction permits empty members and empty underlying spaces.

These are derived consequences of the quasinet and net definitions in
Vladimir G. Berkovich, *Étale cohomology for non-Archimedean analytic spaces*
(1993), section 1.1, printed pp.13–14 / PDF pp.10–11, registered as
`berkovich-1993-etale-cohomology`. The source defines quasinets on p.13
and nets on p.14, with the induced topology on every subset. This module
supplies an internal closure construction from those definitions; it is
not a separately numbered assertion of the source. It provides topology
for later atlas constructions, without asserting affinoid representability
of the intersections.
