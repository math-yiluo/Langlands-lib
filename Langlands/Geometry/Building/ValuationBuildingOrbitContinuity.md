# Orbit continuity from open norm-one point stabilizers

This internal prerequisite concerns the existing action of the actual group
`rationalPoints G` on the existing quotient `B.ReducedBuilding`, for supplied
`B : ValuationBuildingData G` over any nonarchimedean local field in universe `u`.
The group topology is exactly `rationalPointTopology F G.X`.

`HasOpenCompactStabilizers` is the proposition that, for every point `x` of
this quotient, the existing norm-one stabilizer `B.compactStabilizer x` is open
in that group topology. It isolates the openness part of the existing
`HasBoundedOpenStabilizers` predicate.
`hasOpenCompactStabilizers_of_hasBoundedOpenStabilizers` proves the implication
by projecting its openness clause. This is an internal interface definition,
without an assertion that either condition holds.

`isLocallyConstant_orbit_of_isOpen_compactStabilizer` proves that the orbit map
at a point is locally constant whenever its existing norm-one stabilizer
`B.compactStabilizer x` is open. For each group element `g`, the inverse image
of this subgroup under `h ↦ g⁻¹ * h` is an open neighborhood of `g`. Every
element of this neighborhood acts on `x` as `g` does, by the already proved
membership characterization of `compactStabilizer`. Smoothness supplied by
`B.isConnectedReductive` provides local finite type, so the published
`rationalPoint_isTopologicalGroup` makes multiplication continuous for this
precise group topology.

`isLocallyConstant_orbit_of_hasOpenCompactStabilizers` applies this argument at
each point under the named openness condition.
`continuous_orbit_of_hasOpenCompactStabilizers` uses the standard fact that
local constancy implies continuity for every topology on the codomain. The
corresponding `isLocallyConstant_orbit_of_hasBoundedOpenStabilizers` and
`continuous_orbit_of_hasBoundedOpenStabilizers` use the proved implication.
These deductions apply to any metric later constructed on this same quotient,
without changing the action or the rational-point topology.

The argument is derived directly from the Library's stabilizer and topology
interfaces and Mathlib's local-constancy criterion. It uses no additional
external source. This module proves neither openness of the stabilizers nor
existence of building data, a complete nonpositively curved metric, or a
supplied-model comparison. Those are separate construction obligations. In
particular, the bounded-open-stabilizer premise is not a new premise in the
unchanged `IntegralModel.BuildingComparisonStatement`.
