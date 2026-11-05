# A geometric comparison target for supplied reductive integral models

This is an internal construction target and a conditional reduction for the
published `IntegralModel.MaximalCompactStatement`. It does not prove that
target or assert existence of the geometric data.

`BuildingComparison M` refers to the original
`M : IntegralModel 𝒪[F] F G`, its original `integralPoints` subgroup, and an
actual `ValuationBuildingData G`. Its space is exactly that datum's
`ReducedBuilding`, the quotient of the rational-point group times the
root-valuation apartment. The action is the existing quotient action.
The comparison supplies a complete metric, nonpositive curvature in the
published KP midpoint sense, isometric group action, and continuity of every
orbit map for exactly `rationalPointTopology F G.X`. It supplies an actual
special vertex, identifies the original image with its existing
`compactStabilizer`, and requires that the model image fixes no other point.
The compact stabilizer is the actual common rational-character norm kernel
intersected with the full point fixer.

These conditions are explicit construction obligations, rather than assumed
maximality or a selected class of compact overgroups. The metric is supplied
on the existing quotient carrier; this interface imposes no additional
normalization on it. The record does not certify the full corrected
Kaletha–Prasad building axioms, construct integral parahoric models, or claim
that a supplied model already equals a member of a parahoric model family.
Its purpose is to state the precise geometric input used by the reduction.

`BuildingComparisonStatement.{u}` asks for such data for every field, actual
group, and supplied integral model under exactly the generic and full
special-fibre connected-reductivity hypotheses of the published target.
The integer ring, fraction-field inclusion, residue field and quotient map
are the canonical ones. The supplied generic isomorphism and integral-point
map are retained. There is no characteristic restriction and no smoothness,
building, comparison, maximality or Iwasawa premise. Constructing this datum
is a substantial remaining geometric obligation.

The implemented reductions are as follows.

1. `Langlands.Geometry.Metric.KP.exists_fixedPoint_of_isCompact` proves that
   a compact subgroup with continuous orbit maps has a fixed point in a
   nonempty complete NPC metric space under an isometric action. The compact
   image of an orbit is bounded. Restriction to the original subgroup gives
   the bounded action required by the published `boundedActionFixedPoint`.
   The group and metric-space universes are independent.
2. `BuildingComparison.maximalCompact` first uses the already proved
   canonical-integer image compactness. For any compact overgroup `L`, the
   preceding fixed-point theorem produces `y` fixed by `L`. Containment of
   the original image makes `y` fixed by that image, so the supplied
   uniqueness condition identifies it with the displayed point.
   The published `compactSubgroup_le_rationalCommonNormKernel` places every
   element of `L` in the actual common norm kernel. These two facts put
   `L` in the displayed compact stabilizer, hence in the original image.
   Antisymmetry gives the required equality. No compact overgroup is omitted.
3. `maximalCompactStatement_of_buildingComparison` applies this argument
   to every quantified input and gives the exact published
   `MaximalCompactStatement.{u}`, conditional on proving the new
   construction statement.

The module is derived internally from the existing actual quotient action,
the published complete-NPC fixed-point theorem, rational-character
norm-kernel inclusion, and supplied-model compactness. It uses no new
external mathematical result. In particular, the conditional assembly is
not an unconditional proof of either construction statement or maximality.
