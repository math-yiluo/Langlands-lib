# Second countability of actual arithmetic-level model points

This is a derived prerequisite for the countable-base assertion in Section 4,
printed p.9, of Brian Conrad, *Weil and Grothendieck approaches to adelic
points* (December 31, 2011). The paper constructs the level topology from the
local-model product in Section 3 and states the full adelic countable-base
conclusion for separated finite-type schemes in Section 4. The present
level assertion is derived from those constructions; it is not a verbatim
numbered result of the paper.

## Actual objects and scope

`CurvePlaceLevelModelSecondCountabilityStatement` quantifies over a function
field F over a finite constant field k, with the specified compatible
k-algebra and rational-function-field algebra structures. For every finite
set S of the actual curve places, and every finite-type scheme X over the
actual outside-S integer ring `curvePlaceSIntegers k F S`, its actual
relative points valued in `curvePlaceAdeleLevel k F S` are second countable
in exactly `curvePlaceLevelModelPointTopology k F S X`.

`NumberFieldLevelModelSecondCountabilityStatement` asserts the same for every
number field K and finite set S of its finite places. The base is the
actual outside-S integer ring and the value ring is
`numberFieldAdeleLevel K S`. This full level retains every archimedean
completion, the finite completions at S, and completed integer rings outside
S, with their original scalar actions. The topology is precisely
`numberFieldLevelModelPointTopology K S X`.

In each case finite type is expressed by `LocallyOfFiniteType X.hom` and
`QuasiCompact X.hom`. The empty set S is allowed. The statements retain
nonaffine schemes and impose no separatedness or quasi-separatedness
assumption. They quantify in an arbitrary common universe.
`AdelicLevelModelSecondCountabilityStatement` is their conjunction.

## Derivation and remaining work

The places of a global field are countable. Each completed local field is
second countable, and each completed integer ring inherits second
countability as a subspace. These actual local factors are local
topological rings with open units and continuous inversion. Finite-type
local-model point spaces are consequently second countable by the
finite-coordinate and finite-affine-cover argument derived from
Propositions 2.1 and 3.1, printed pp.2 and 4. The countable product of these
local point spaces is second countable. The defined arithmetic level
topology is induced from that product, so it is second countable as well.
Second countability of an induced topology does not require the inducing
map to be injective or surjective.

This pair declares a proposition target. Its proof is a separate
contribution. Passing to the full adelic final topology and transporting to
generic-fibre point spaces require further arguments and are not asserted
here.

## Source

Registered source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`:
Propositions 2.1 and 3.1, printed pp.2 and 4; Section 3's level product
construction (3.6.1), printed p.8; Section 4's countable-base assertion,
printed p.9.
