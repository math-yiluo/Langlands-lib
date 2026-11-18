# Gauge integrability for the equal-rank unfolding

`Langlands.Global.RankinSelbergGlobal.equalUnfoldingGauge` proves exactly
the existing proposition `EqualUnfoldingGaugeStatement.{u}`. It supplies
both the ordinary and dual gauge premises for every number field
`F : Type u` with compact additive adelic quotient, every natural `r`,
and every pair of actual cuspidal realizations of rank `r + 1`.

The implemented proof is the application
`equalGaugeAnalyticReduction.{u} whittakerSchwartzGauge.{u}`.
The published theorem `whittakerSchwartzGauge` proves the general
weighted Whittaker–Schwartz estimate without an additional gauge or
convergence hypothesis. The published reduction
`equalGaugeAnalyticReduction` turns that estimate into the conjunction
that defines the target.

For the first conjunct, the reduction applies `equalGaugeSpecialization`
to the actual cusp-function space. Its decay class and common central
power bound give the weighted Whittaker–Schwartz bound for each
realization. The theorem `equalGaugeReduction` absorbs the second cusp
function using its common central exponent and transfers the finite
majorant integral to the rational unipotent quotient. This proves
`EqualWhittakerGaugeIntegrable F T T'`.

For the second conjunct, `equalGaugeDualSpecialization` applies the same
general estimate to the transpose-inverse cusp space. The inverse
standard additive character and the dual Whittaker identity identify
the required dual Whittaker function. The dual central bound, Fourier
stability of Schwartz–Bruhat functions and quotient integration then
give `DualEqualWhittakerGaugeIntegrable F T T'`.

In each conjunct, the nonnegative threshold is chosen before the
standard character, both vectors, the Schwartz–Bruhat function and the
complex integration parameter. It may depend on the field, rank and
pair of realizations. The integrability conclusions use the original
measure `LeftCosetSpace.haarQuotientMeasure
(unipotentRationalImage F (r + 1)) _` on
`N_(r+1)(F) \ GL_(r+1)(𝔸)`. The dual conclusion is stated, as in the
target, at a parameter with real part above its threshold.

The provenance is internal composition of the two named published
theorems and their existing cusp-space specializations. The proof
retains the field universe `u`, all target hypotheses, and both actual
quotient measures and kernels. It changes no target or imported
definition. The analytic and specialization arguments are implemented
in the imported modules described above.
