# Axiom 4.1.2 under based group isomorphisms

Module `Langlands.Geometry.Building.FullValidity.DatumTransport.Bounded`.

## Purpose and provenance

Internal infrastructure for `KPBuildingDatumTransportStatement`: KP Axiom 4.1.2 (stabilizers
of points are bounded open subgroups) is preserved by the transport of
`DatumTransport.Building`. Not stated separately in the source.

## Contents

- `DatumTransport.isOpen_isAlgebraicallyBounded_map`: the image of an open algebraically bounded
  subgroup of `G(F)` under `f` is open and algebraically bounded in `H(F)`. Openness: the image
  is the preimage of the subgroup under the point map of `f⁻¹`, which is continuous
  (`continuous_rationalPointMap`). Boundedness: the Library's
  `IsAlgebraicallyBounded.image_rationalPointsMap`.
- `HasBoundedOpenStabilizers.basedTransport`: every point of the target building is the image
  of a source point, whose norm-one stabilizer is carried onto the target norm-one stabilizer by
  `map_compactStabilizer_basedTransport`.
