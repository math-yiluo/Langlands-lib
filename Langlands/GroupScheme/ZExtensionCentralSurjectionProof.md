# Ascent of simply connected derived groups along central surjections

`Langlands.GroupScheme.simplyConnectedDerivedAscent` proves
`Langlands.GroupScheme.SimplyConnectedDerivedAscentStatement`.
It works over every field for a surjective homomorphism `p : E ⟶ G`
between connected reductive groups with central full kernel.

The proof obtains an actual derived-subgroup inclusion `d : D ⟶ E`
from `derivedSubgroupRepresentability`; the required affine and locally
finite type instances come from the connected reductive hypothesis.
It obtains `d' : D' ⟶ G` and `IsSimplyConnected D'` by unpacking the
given `HasSimplyConnectedDerivedGroup G`.

The published `derivedSubgroupSemisimple` makes `D` semisimple, and
`IsDerivedSubgroup.isCentralIsogeny_map` makes the induced map
`hd.map hd' p : D ⟶ D'` a central isogeny. The defining criterion
`IsSimplyConnected.central_isogeny_isIso` therefore makes this map an
isomorphism. `IsSimplyConnected.of_iso` transports simple connectedness
from `D'` to `D`, supplying the required actual derived subgroup of `E`.

`HasSimplyConnectedDerivedGroup.of_centralSurjection` is the same result
with implicit field and group variables for use in the z-extension
fiber-product construction. The proof uses only published Library
results and the statement module; it assumes neither a dominating
z-extension nor any desired commuting equality.
