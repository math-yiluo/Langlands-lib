# Conditional assembly of twisted-stable chambers

This module gives two conditional reductions to
`UnramifiedTwistedChamberStatement.{u}` at arbitrary universe `u`. It does not
prove the unconditional target. Metric existence and the residual
chamber-through-fixed-point statement remain outstanding inputs.

`UnramifiedTwistedChamberReductionStatement.{u}` is the Prop-valued
definition
`UnramifiedBuildingMetricStatement.{u} →
UnramifiedTwistedChamberThroughFixedPointStatement.{u} →
UnramifiedTwistedChamberStatement.{u}`.
The theorem `unramifiedTwistedChamberReduction` proves this conditional
statement using `unramifiedTwistedChamber_of_metric` below.

`unramifiedTwistedChamber_of_fixedPoint` assumes
`UnramifiedTwistedFixedPointStatement.{u}` and
`UnramifiedTwistedChamberThroughFixedPointStatement.{u}`. It specializes the
fixed-point statement to the exact original group, torus, apartment,
centralizer and cocycle data. It supplies the resulting point and fixedness
formula to the residual statement and projects its chamber and stability
clauses. The closure-incidence clause is not needed for this conclusion.
Both applications retain the same reduced-building carrier, original
coefficient action and cocycle twist. The local affine and monomorphism
instances are derived from the target hypotheses.

`unramifiedTwistedChamber_of_metric` assumes
`UnramifiedBuildingMetricStatement.{u}` and
`UnramifiedTwistedChamberThroughFixedPointStatement.{u}`. It first applies the
proved reduction `unramifiedTwistedFixedPoint_of_metric`, then the preceding
assembly. Thus the finite-orbit and bounded-action fixed-point route in the
imported reduction supplies the intermediate point.

The provenance is internal composition of the imported statements and proved
reduction. No new literature assertion is made. Neither conditional theorem
uses a proof of a downstream simply-connected chamber or cocycle-vanishing
statement, and neither supplies either of its two assumed statements.
