# Changing variables in `L²` under a positive finite measure rescaling

`Langlands.MeasureTransport.l2Equiv` is the continuous complex linear equivalence given by composition with a measurable equivalence \(e\) satisfying \(e_*\mu=c\nu\), for \(0<c<\infty\). Its inverse composes with \(e^{-1}\). Both formulas hold almost everywhere at the level of representatives.

This is the change-of-variables identity for \(L^2\). In Lean, `MeasurableEquiv.map_ae` and the equality of null filters after nonzero rescaling give the almost-everywhere comparison. A class is pulled back using `MemLp.comp_measurePreserving` for the scaled measure. The norm computation combines `eLpNorm_comp_measurePreserving` and `eLpNorm_smul_measure_of_ne_zero_of_ne_top`, giving a homothety of factor \(\sqrt c\). `ContinuousLinearEquiv.ofHomothety` supplies continuity of both linear maps.
