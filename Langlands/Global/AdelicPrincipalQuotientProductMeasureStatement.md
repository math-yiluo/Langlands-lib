# Exact product measure on the full principal adelic quotient

`Langlands.Global.RestrictionSplitCentre.PrincipalQuotientProductMeasureStatement`
is the proposition that, for a number field `F` and an affine, locally finite
type connected reductive `F`-group scheme `G`, the measurable equivalence

\[
G(F)\backslash G(\mathbb A_F) \;\longrightarrow\; A_G\times [G],\qquad
[an]\longmapsto (a,[n])
\]

is measure preserving. The source measure is the Library's existing
`AdelicGroupPoints.rationalQuotientHaarMeasure`: the ambient Haar quotient
with counting normalization on the actual rational image. The target is
`positiveCentreHaarMeasure.prod canonicalMeasure`. In the first factor the
central Haar is scaled so that its product with the fixed norm-one Haar
reproduces the fixed ambient Haar under multiplication. The second factor
is the existing measure on `[G]`, obtained from the count-normalized
norm-one principal quotient measure. No scalar relating the two sides is
left over, and neither quotient measure is changed. There is no premise of
unimodularity, finite volume, or a supplied splitting or normalization.

This is a derived measure statement for the Getz–Hahn number-field split
centre and quotient conventions (*An Introduction to Automorphic
Representations*, 2024, §2.6, pp. 68–69, PDF pp. 85–86,
(2.19)–(2.22) and Lemma 2.6.2), not a numerical measure formula cited
from them. The proof obligation is to apply the discrete quotient product
law to the intrinsic multiplication chart and then push the two factors
through the positive image and norm-one quotient comparisons. The exact
identity is useful for comparing pairings on the two quotients; it does not
itself assert that the wave packets factor through that product.
