# Continuous representatives on the positive rational quotient

`Langlands.Automorphic.GroupSchemeFunctions.groupSchemeQuotientL2ContinuousRepresentative`
proves `GroupSchemeQuotientL2ContinuousRepresentativeStatement` for the
original integrated right action on the positive rational quotient \(L^2\).

## Proof

Let \(H\) be `positiveRationalSubgroup F G T i`. The proof applies
`Langlands.QuotientIntegration.quotientIntegratedContinuousRepresentative`
to \(H\) and the published ambient, subgroup and quotient measures.
`isClosed_positiveRationalSubgroup` supplies closedness, and the published
measure facts give the Borel structure of the quotient, finiteness on
compact sets and the subgroup measure's σ-finiteness and right invariance.
`positiveRationalQuotientHaarMeasure_isCompatible` gives the Weil
compatibility for these normalizations.

The action supplied to the generic theorem is
`haarQuotientL2BoundedRightAction`, with its norm identity and almost
everywhere strong measurability of its orbits. By
`coeFn_quotientL2RightTranslate`, each orbit value is represented almost
everywhere by pullback along `LeftCosetSpace.rightTranslate`. Quotient
induction checks that this translation and the generic translation both
send \([x]\) to \([xg]\). The shared coset carrier and the definition of
`haarQuotientL2IntegratedAction` let the generic conclusion apply directly.
It gives the continuous representative, its almost-everywhere equality
with the integrated class, and the bound
\[
  \lVert\psi([x])\rVert^2
  \le M\left(\int \lVert f(a)\rVert\,d\mu_G(a)\right)
     \mu_H^{\mathrm{real}}(H\cap x S x^{-1})\,\lVert\phi\rVert^2.
\]
Here \(M\) is any uniform bound for \(\lVert f\rVert\), and
\(S = \operatorname{tsupport}(f)\operatorname{tsupport}(f)^{-1}\).
The subgroup measure is evaluated on the preimage of \(x S x^{-1}\)
under the inclusion of \(H\).

## Provenance

Getz and Hahn use bounded point evaluations of convolution in Lemma 9.3.3
and (9.13), printed pp. 247–248 (PDF pp. 259–260). The first line of
(9.14), printed p. 250 (PDF p. 262), writes the pointwise convolution
integral. The explicit coset-dependent bound comes from the Library's
general quotient convolution theorem. [J. R. Getz and H. Hahn, *An
Introduction to Automorphic Representations* (2024)](https://doi.org/10.1007/978-3-031-41153-3).

Registered source `getz-hahn-2024-automorphic-representations`, SHA-256
`a125cf9c0f445972cbbd3552b4fb9905ca948108a05880f90eaa43558d09a507`.
