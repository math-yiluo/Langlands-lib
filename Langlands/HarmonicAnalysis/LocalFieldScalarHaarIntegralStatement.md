# Scalar change of variables for local-field Haar integrals

`Langlands.HarmonicAnalysis.LocalFieldScalarHaarIntegralStatement` states the
integral identity
\[
\int_F f(ax)\,d\mu(x)=|a|_F^{-1}\int_F f(x)\,d\mu(x).
\]
Here \(F\) is a nonarchimedean local field of either characteristic, \(\mu\)
is a Borel additive Haar measure, \(a\) is a field unit and `SchwartzBruhat F`
consists of locally constant compactly supported complex functions. The
absolute value is the residue normalization
`Langlands.LocalField.residueNormalizedAbsoluteValue`.

This is the change-of-variables formula in David Renard,
*Représentations des groupes réductifs \(p\)-adiques*, 9 July 2026,
§ V.1, printed p. 104 (PDF p. 110).
