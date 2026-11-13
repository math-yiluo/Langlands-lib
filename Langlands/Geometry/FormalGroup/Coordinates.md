# Pointed formal-coordinate maps and nilpotent tuples

This internal foundation represents a pointed map between finite-dimensional
formal affine spaces over a commutative ring by a tuple of multivariable
power series with zero constant term. The source and target coordinate
sets may be arbitrary finite types. Composition substitutes the tuple of
the first map into each series of the second map.

`CoordinateMap` includes identities, zero maps, projections, selected
variables and pairing. Its composition laws and product identities are
proved with Mathlib's substitution homomorphisms. `SeriesPoint` consists
of tuples whose constant coefficients are nilpotent; all target power-series
variable sets are permitted. Evaluation is substitution and preserves this
condition. Its composition, identity and pairing laws are proved.

`SeriesPoint.nilpotentEquiv` identifies the case with no formal variables
with the tuples of nilpotent elements of the coefficient ring. No topology
or convergence data is supplied by the caller: finite-dimensional
substitution is available because the constant coefficients are nilpotent.

This is an implementation foundation for the formal groups used in
Drinfeld, *Coverings of p-adic symmetric regions* (1976), §1, printed
p.108 and the gluing convention on p.109. Source ID:
`drinfeld-1976-coverings-p-adic-symmetric-regions`; content SHA256:
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The coordinate-map and evaluation API is derived implementation content,
not a separately asserted theorem in that paper. It uses Mathlib's
`MvPowerSeries.Substitution` and `MvPowerSeries.Equiv`. It does not yet
define formal group laws or groups glued from coordinate charts.
