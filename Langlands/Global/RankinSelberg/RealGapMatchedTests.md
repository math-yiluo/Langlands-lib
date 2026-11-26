# Matching the split tests in the two real Godement integrals

This module is the real counterpart of the Library's `ComplexGapMatchedTests`. Notation as in
`RealGapDualArguments` and `RealGapAlternateRestriction`; `T` is a `GodementColumnFactors k q`,
`𝓕_a = realFourierTransform a` the Fourier transform of column tests, and `ψ_a` the character of
`realSelfDualMeasure a`.

* `tailFactor a T C = T.tail_{q+1}(tailColumn C 0) · ∏_{j ≤ q} 𝓕_a(T.tail_{q−j})(tailColumn(ι C, j))`.
  `tailFactor_reverse` rewrites it in the head, final-frequency and later coordinates of the ordinary
  chart.
* `alternateBlockTailKernel_reverse`: with `C = B · packedTail 0 Z`, the alternate tail kernel of
  `RealGapTailExchange` for the reversed factors `reverseTail T` is
  `T.leading(leading(C · A h)) · tailFactor a T C · W(A(g h^{-1}) · C^{-1}) · χ(det h) · χ(det C)`.
* `dualFiber a c F T Ud g h C V X` is the padded restriction kernel of `RealGodementPaddedRestriction`
  for the character datum `c⁻¹` (`c.inverse`), the parameter `−a`, the square factor
  `realRectangularSchwartzFourier a F`, the last factor `realRowSchwartzFourier a (T.tail_{q+1})` and the
  function `Ud`. It is evaluated at `g' = A(g)`, `b = lowerShear X` and the point `dualMatrix C h V`.
  These are the factors of the transformed separated test
  `realRectangularSchwartzFourier a (realColumnProduct F (T.tail_{q+1}))`
  (`RealJacquet.realColumnProduct_fourier`).
* `dualFiberFactor a c T Ud g h C V = tailFactor a T C · Ud(lowerPoint(g · ι₁(h)^{-1}, V) · w · ι(C)^{-1}) ·
  restrictionWeight k q c⁻¹ (det(dualMatrix C h V))`.

`RealGapMatchedTestsStatement` (proved by `realGapMatchedTests`): let `F` be a Schwartz function on
`n × n` matrices with `F = squareEval T`. For every `Ud`, `g`, `h`, `V` and every `C` with `|det C| = 1`,
the function `X ↦ dualFiber a c F T Ud g h C V X` is integrable for `rectangularMeasure μ (q+1) k`,
`μ = realSelfDualMeasure a`, and its integral is

`rectFourier a (leadingRestriction k (q+1) k C T.leading) (ι₁ h) · dualFiberFactor a c T Ud g h C V`.

The proof computes the dual fiber pointwise. The square factor is `squareEval (fourierFactors a T)` by
`realGapSplitFourier`. The arguments are those of `realGapDualArguments`, and the last factor is
transformed back by the inversion `realRowSchwartzFourier_neg_comp`. The reversed product of the tail
transforms is reindexed to the tail factor. The measure-preserving shear of the complementary rows and
the leading Fourier identity `realGapLeadingFourier` (with `|det C| = 1`) then give the integral and its
absolute convergence. This is the computation between (10.7) and (10.10) of Jacquet, *Archimedean
Rankin–Selberg integrals* (2009), §10.3.
