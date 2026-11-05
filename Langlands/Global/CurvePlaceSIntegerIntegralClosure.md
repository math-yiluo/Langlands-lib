# Actual function-field S-integer integral closure

This derived construction supplies the integral-closure identification needed by
Conrad, *Weil and Grothendieck approaches to adelic points* (2011), Example 4.2,
printed pages 9–10. For a finite extension of the original function field over
finite constants, the integers outside the full upper preimage of any finite
lower exceptional set are exactly the integral closure of the lower outside-set
integer ring in the original upper field. The resulting ring equivalence is the
identity on upper-field elements.

For each lower place outside the exceptional set, the published local criterion
`CurvePlaceIntegralLattice.integral_mem_iff` identifies local integrality with
membership in every upper valuation ring. Full-preimage membership supplies all
these upper tests. The local valuation ring is integrally closed with the
original lower field as fraction field, so its monic minimal polynomial maps to
the minimal polynomial over that field. Every coefficient of the latter is
therefore integral at every required lower place. The coefficientwise lifting
criterion constructs a polynomial over the actual lower S-integer ring; its
injective map is the original monic minimal polynomial. Evaluation in the upper
field proves integrality. The reverse inclusion was proved for the extension map
in `ArithmeticSIntegerExtension` by upper valuation-ring integral closedness.

All fields inhabit an arbitrary common universe. Compatible constant-field
algebras, a scalar tower, finite constants, a lower function-field presentation
and a finite original field extension are explicit. No separability assumption
is imposed. Empty exceptional sets are allowed: the coefficient argument does
not assume that the lower S-integer ring has the whole original lower field as
its fraction field. Finite local freeness and the integral and adelic Weil
comparisons remain obligations of the host task.
