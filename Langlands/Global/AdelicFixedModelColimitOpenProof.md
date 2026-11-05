# Open arithmetic stages in actual full-adele model points

`Langlands.Global.adelicFixedModelColimitOpen` proves the exact proposition
`AdelicFixedModelColimitOpenStatement` in an arbitrary common universe.
The separate curve and number-field theorems prove its two constituents.
The maps, coefficient actions, arithmetic stage topologies and final
full-adele point topologies are precisely those of the target.

For each branch, the proof specializes `filteredRingPointOpenStages` to
the actual fixed-base arithmetic algebra diagram and its stage topologies.
The continuity and openness hypotheses follow from
`adelicFixedModelTransitionTopology`, with each categorical morphism
interpreted as inclusion of finite superlevels. The finite-type bijection
`adelicFixedModelFiniteType` upgrades the canonical point comparison to
`ringPointColimitHomeomorph`, using the independently defined final
topologies.

Stage continuity follows directly from the final topology. Composing the
generic open stage maps with the comparison homeomorphism proves their
openness in actual full-adele points. Composing the generic open embeddings
of quotient-topologized stage images with that same homeomorphism proves
the second clause without assuming separatedness. Under separatedness,
the arithmetic transition theorem gives open embeddings and hence
injective transitions. The last part of `filteredRingPointOpenStages`
then gives open stage embeddings into the colimit, which the comparison
homeomorphism transports to actual full-adele points.

This is an internal specialization of the published generic colimit
argument to the actual arithmetic construction, following Conrad,
*Weil and Grothendieck approaches to adelic points* (December 31, 2011),
equation (3.5.1) and Theorem 3.6 on printed p.6, the transition argument
on p.8, and the quotient-image discussion opening Section 4 on p.9.
The proof retains the target's arbitrary constants with compatible
function-field scalar tower, empty initial finite sets, all infinite
number-field factors, and arbitrary nonaffine finite-type models.
It adds no model-independence, generic-fiber, compactness or separation
conclusions beyond those stated in that target.
