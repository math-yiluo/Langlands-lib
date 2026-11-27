# Compactness of continuous cuspidal convolutions

`Langlands.Automorphic.GroupSchemeFunctions.GroupSchemeFullAEL2CuspidalCompactnessStatement`
concerns a connected reductive affine group scheme \(G\) locally of
finite type over a number field \(F\). It uses `ParabolicDynamicStatement`
to form the proper rational parabolic radical family. It takes a central
morphism \(i:T\to G\) from a torus with a supplied finite-rank splitting
and assumes that its restriction of rational characters is injective
with finite-index image. Haar measure on \(G(\mathbb A_F)^1\), the common
kernel of the rational character norms, is assumed right invariant.

The quotient is \(A_iG(F)\backslash G(\mathbb A_F)\), where \(A_i\) is
the image of the positive real coordinates of \(T\) at the infinite
places. Its measure `positiveRationalQuotientHaarMeasure` is pushed
forward from the norm-one rational quotient by inclusion.
`fullAEL2CuspidalSubmodule` is the closed space where the normalized
periods along all proper rational parabolic radicals converge and vanish
almost everywhere in the norm-one variable. The period measures have
mass one. For every continuous compactly supported complex weight on
\(G(\mathbb A_F)\), the original integrated right action on that space
against full adelic `Measure.haar` is compact.

This is a consequence of the cuspidal trace-class theorem for smooth
weights in Getz–Hahn, *An Introduction to Automorphic Representations*
(2024), Theorem 9.1.2, printed p. 241 (PDF p. 253), and the use of
compact convolution operators in Lemma 9.3.1 and Corollary 9.3.2,
printed p. 247 (PDF p. 259). For the quotient convention see
§2.6, (2.19)–(2.22) and Lemma 2.6.2, printed pp. 68–69 (PDF pp. 85–86).
When \(i\) is a split component, the Library identifies \(A_i\) with
the canonical \(A_G\) of (2.20) by
`RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup`.
The exact group and function scopes here use full adelic test weights
for the smooth input and extend compactness to continuous compactly
supported weights by approximation in the integrated operator norm.
