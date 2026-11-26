# Joint convergence on the full real dual chart

This module is the real counterpart of the Library's `ComplexGapDualHaar`.

* `lowerRectangle_eq_lowerShear` identifies the lower rectangle insertion of `RealGodementLowerRectangle`
  with the consecutively indexed `lowerShear`; `detAbs_dualChart` shows that the dual chart has the
  absolute determinant of the inverse transpose of its leading matrix (the retained matrix, the tail
  reversal and the lower shear have absolute determinant one).
* `dualChartMeasure a η₁ κ` is the measure `unitOuterMeasure × (rectangle Haar × entryHaar)` of the dual
  chart for the self-dual measure of `a`, an arbitrary Haar measure `η₁` on `GL_(t+1)(ℝ)` and a measure `κ`
  on the orthogonal group; it is σ-finite for Haar `η₁`, `κ` (`sigmaFinite_dualChartMeasure`).
* `dualChartWeightedKernel a c Fs T Wd Vd f₁ f₂` is the full dual kernel on the quotient, the complementary
  rectangle and the dual chart, with weights `f₁` at the quotient determinant divided by the leading
  determinant and `f₂` at the leading determinant. `dualChartWeightedKernel_eq` identifies it with the
  pullback along the dual chart of `coupledHaarKernel` for the inverse character, the parameter `−a`, the
  rectangular Fourier transform of `Fs` and the row Fourier transform of `T.tail last`.

`RealGapDualHaarStatement` (proved by `realGapDualHaar`): for Haar `η₁`, `κ` with `κ` inversion invariant,
`Wd` in `realUniformWhittakerModel (t+1+q) ds a`, `Vd` in `realUniformWhittakerModel t es (−a)`, a Schwartz
`Fs = T.squareEval`, and measurable rapidly decaying `f₁`, `f₂`, the kernel is integrable for the quotient
measure times the complementary rectangle times `dualChartMeasure`. `realGapDualHaarPowerBounds` allows two
independently large power bounds instead of rapid decay.

## Proof

`realGapSplitFourier` and `realGapPartialFactors` at `−a`, applied to the Fourier factors of `T`, give the
split test for the transformed square test; Fourier inversion on rows (`realRowSchwartzFourier_neg_comp`)
gives the frequency factor `T.tail last`. `realGapCoupledHaarPowerBounds` then gives integrability against
a Haar measure on `GL_(t+1+q+1)(ℝ)`, which `realGapDualChart` writes as a positive multiple of the image of
`dualChartMeasure`; pulling back along the chart gives the statement.

This is the dual-chart convergence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.4,
Lemma 10.7, pp. 79–81.
