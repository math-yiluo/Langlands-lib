# Change of additive character for arithmetic pair epsilon factors

`Langlands.Correspondence.isArithmeticPairEpsilonFactor_zeroMonodromy_scale` computes the change of a zero-monodromy pair epsilon certificate for continuous local Weil representations \(A,B\). For \(a=\operatorname{rec}(w)\), using the bottom reciprocity candidate of the system, put \(N=\dim A\dim B\). Replacing \(\psi(x)\) by \(\psi(ax)\) sends the coefficient \(c\) and exponent \(m\) to

\[
 c\,\det A(w)^{\dim B}\det B(w)^{\dim A}|a|^{-N/2},
 \qquad m+N\operatorname{ord}(a).
\]

`isArithmeticPairEpsilonFactor_zeroMonodromy_iff` evaluates each certificate at the canonical bottom-field data. `isSelfDual_scale` and `eq_localSelfDualHaar` show that scaling the character multiplies the self-dual measure by \(|a|^{1/2}\). The system's Haar-scaling law gives \(|a|^{N/2}\), and `LocalFactor.NonabelianSystem.additiveCharacterScaling` gives the twisted determinant and \(|a|^{-N}\) at the fixed measure. `det_tensorProduct_map` and `det_twist` compute the twisted determinant. The bottom-field reciprocity normalization identifies \(\operatorname{ord}(a)\) with the Weil degree of \(w\), giving the shift in the exponent.

The formula combines Deligne's fixed-measure law, *Les constantes des équations fonctionnelles des fonctions L*, (5.4), manuscript p. 48, with self-dual Haar scaling. It supplies the arithmetic change of character in `Langlands.Global.PoleComparison.RelativeIsometryFactorStatement`.
