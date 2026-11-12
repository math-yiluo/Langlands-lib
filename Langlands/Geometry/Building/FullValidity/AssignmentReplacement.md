# Replacement of full KP assignment entries

This is internal derived infrastructure for changing supplied KP data. It uses
`KPBuildingAssignment.isAvailableFor_iff` and
`ValuationBuildingData.IsEquivariantBuildingIso.trans` from the published
`FullValidity.Assignment` module.

`KPBuildingDatum.BuildingEquivalence` supplies both oriented geometric comparison
clauses and identity equivariance. It includes no validity assumption.
`isValid_of_buildingEquivalences` transfers all four cross-group comparison
predicates by composition with the inverse comparison at the source and the
forward comparison at the target. Group axioms for the replacement data are
supplied separately, without dropping any of their nine fields.

`DatumIndex` bundles all field structures and the affine connected reductive
group. `replaceDatum` uses dependent function update on that index. This retains
the original assignment at all unequal indices, and gives the prescribed datum
at the chosen one. `replaceDatum_isValid` proves full validity by the pointwise
comparison theorem, using the supplied group axioms and comparison at the new
entry and the original group axioms and identity comparison elsewhere. Bundling
includes the valuation and topology, so equality of underlying field types alone
never identifies two inputs.

This module does not construct a torus transport of full KP data and does not
prove that a valid assignment exists.
