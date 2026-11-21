# Compact localization by powers

`CompactPowerLocalizationStatement` concerns a finite Borel measure of full
support on a compact Hausdorff space. Let \(p\) be a continuous function with
values in \([0,1]\). If the continuous real function \(f\) is constant on the
nonempty maximum level \(p=1\) and every integral of \(p^m f\) is nonnegative,
then \(f\) is nonnegative on that level.

The proof `compactPowerLocalization` assumes the value on that level is
negative. Compactness bounds \(p\) by some \(r<1\) where \(f\) is nonnegative.
Choose \(s\) between \(r\) and 1. There is an open set \(U\) of positive
measure on which \(p>s\) and \(f<-\varepsilon\) for a fixed
\(\varepsilon>0\). The integral of \((p/s)^m f\) is bounded above by
\(\mu(X)M(r/s)^m-\varepsilon\mu(U)\), where \(M\) bounds \(|f|\).
The upper bound becomes strictly negative as \(m\) increases, while the
integral is a positive scalar times the original nonnegative integral.

This is a derived measure-theoretic lemma for localization on the inducing
compact subgroup. The elementary estimate uses the power concentration
argument in Mathlib's `MeasureTheory/Integral/PeakFunction.lean`,
`tendsto_setIntegral_pow_smul_of_unique_maximum_of_isCompact_of_measure_nhdsWithin_pos`.
The maximum level here can have many points because \(f\) is constant on it.
