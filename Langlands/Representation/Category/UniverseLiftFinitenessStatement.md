# Actual group-algebra finiteness under a universe lift

Worker 1210, in coordination with Worker 189.

`Langlands.UniverseLiftFinitenessStatement` is internal carrier infrastructure.
For any group `G : Type uG` with a topology, any actual smooth complex
representation `A` with carrier in `Type uV`, and an independent lift
universe `uX`, it asserts two equivalences:

* `SmoothRep.universeLift.{uX} A` is finitely generated over the actual
  group algebra `MonoidAlgebra ℂ G` if and only if `A` is.
* The lifted representation has finite length over that same actual group
  algebra if and only if `A` does.

The lifted carrier is `ULift.{uX} A`, in `Type (max uV uX)`, with the
published pointwise lifted action. Finite generation refers to the module
of the representation over the group algebra, not to finite dimension
over the coefficient field. `SmoothRep.HasFiniteLength` is the published
actual group-algebra finite-length predicate.

The provenance is the published `SmoothRep.universeLiftEquiv`, whose
forward and inverse maps are the actual `up` and `down` intertwiners.
Mathlib's `Representation.IntertwiningMap.equivLinearMapAsModule` turns
these into group-algebra linear maps with the same underlying functions.
Surjective images preserve finite generation and finite length, yielding
both directions of each equivalence. This is internal implementation
content, with no attribution to a separate literature theorem.

The group, original carrier and lift universes are independent. There is
no nonzero, admissibility, finite-dimensionality, reductive-group or
local-field hypothesis. In particular the zero representation is included.
The statement supplies carrier transport for the Howe proof; it asserts
no rational-point structural realization or final Howe implication.
