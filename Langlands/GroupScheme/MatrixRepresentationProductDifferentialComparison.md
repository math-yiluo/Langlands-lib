# Actual analytic and dual-number product differential comparison

`Langlands.GroupScheme.MatrixRepresentation.analyticProductDifferentialComparison`
proves exactly the published proposition
`AnalyticProductDifferentialComparison (B := B) ρ` for every genuine matrix
representation of the stated finite product of general linear schemes.

The proof lifts the line `1 + s • X` near zero through the actual open
matrix-units chart. Openness ensures that this curve has matrix values equal
to the line in a neighborhood of zero. Those matrix values have derivative
`X`; composing the derivative of ring inversion at the identity gives derivative
`-X` for the inverse matrices. Entry evaluation therefore gives exactly the
value and epsilon coefficients of the independently defined units `I + εX`,
whose inverse is `I - εX`.

The regular-function jet detector extends this match from entries and inverse
entries to all regular functions and assembles the finite factors. Worker
1650's paired `MatrixRepresentationProductOutputJet` helper postcomposes this
actual jet with the representation and evaluates the output entry sections.
The published epsilon-coefficient formula identifies those entry derivatives
with `ρ.productDifferential B X`.

Independently, the published actual Frechet derivative, composed with the line,
gives derivative `ρ.analyticProductDifferential X`. The chart extension agrees
with the evaluated representation along the lifted curve near zero. Uniqueness
of ordinary real derivatives identifies the two matrices entry by entry.

This is internal compatibility mathematics. It assumes no differential formula
or comparison hypothesis and leaves the published target and its mathematical
imports unchanged. The arbitrary base commutative ring `R` and finite factor
index `J` have shared universe `u`; all matrix indices are small finite types.
The coefficient algebra is any complete normed commutative real algebra `B`
with the given `Algebra R B`. No topology or continuity assumption on `R` is
used. Empty factor and matrix index types, including zero ranks, remain in
scope. Worker 1607 constructed the jet infrastructure and curve argument;
Worker 1650 supplied the output-entry bridge.
