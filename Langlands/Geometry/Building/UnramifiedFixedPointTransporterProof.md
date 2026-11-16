# The split-centralizing transporter of special apartments over the maximal unramified extension

The theorem `Langlands.Geometry.Building.unramifiedFixedPointTransporter` proves
the published proposition
`Langlands.Geometry.Building.UnramifiedFixedPointTransporterStatement`. It holds
in arbitrary universe `u` and for both characteristics. It adds no hypotheses:
its type is exactly that proposition. This is the Library formulation of
Kaletha–Prasad Proposition 9.3.11(1), together with Proposition 9.3.12, over the
maximal unramified extension \(K\).

## Proof

The proof is a single application of two published Library theorems:

- `Langlands.Geometry.Building.unramifiedFixedPointTransporter_of_fixedPairSpecialApartment`
  (module `Langlands.Geometry.Building.UnramifiedFixedPointTransporterReduction`).
  It proves the implication
  `UnramifiedFixedPairSpecialApartmentStatement.{u} → UnramifiedFixedPointTransporterStatement.{u}`.
- `Langlands.Geometry.Building.unramifiedFixedPairSpecialApartment`
  (module `Langlands.Geometry.Building.UnramifiedFixedPairSpecialApartmentProof`).
  It proves `UnramifiedFixedPairSpecialApartmentStatement.{u}`: two
  coefficient-fixed, torus-unit-fixed points lie in one centralizing translate
  of the given special apartment, and the coefficient differences take values
  in the normalizer.

Applying the reduction to the two-point theorem, at the same universe `u`, gives
the target.

## Inputs used through these theorems

These are the main published inputs behind the two theorems:

- The reduction uses the published Levi sharp transport
  `Langlands.Geometry.Building.unramifiedLeviSharpApartmentTransport`, which
  takes the place of KP 9.3.12. It also uses the torus-unit fixation lemma
  `isFixedByScalarTorusUnits_apartmentMap` from
  `Langlands.Geometry.Building.TorusUnitApartmentFixation`. Its Markdown
  describes the argument.
- The two-point theorem uses
  `Langlands.BruhatTits.IntegralModels.recoveredFixedBuildingPairModels` and
  `Langlands.Geometry.Building.unitFixedPairApartmentOfNeutralModel`. Its
  Markdown describes the argument.

Neither theorem uses any proposition that the task excludes, directly or
indirectly. The transitive imports of both modules mention none of
`UnramifiedTorusUnitFixedApartmentStatement`,
`UnramifiedTorusUnitFixedApartmentReductionStatement`,
`UnramifiedGaloisFixedBuildingPointStatement`,
`UnramifiedBuildingDescentStatement`,
`UnramifiedBuildingDescentReductionStatement` or
`UnramifiedBuildingDescentRemainingReductionStatement`.
