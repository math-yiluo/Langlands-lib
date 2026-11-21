# Vanishing of eigendistributions supported on a zero section

`Langlands.HarmonicAnalysis.ZeroSectionFieldVanishingStatement` concerns
complex-valued distributions on a product of real open sets. Assume the
distribution vanishes on tests supported off the zero normal section and
has a nonzero eigenvalue for differentiation along a smooth vector field
plus a smooth scalar multiplier. If both the field and the multiplier
vanish along the section and the field derivative there is nilpotent, then
the distribution is zero.

The Lean proof restricts to smaller product balls whose compact closures
fit in the test domain. On such a restriction a distribution supported on
the section has finite transverse order. For a test with zero lower
transverse derivatives, the corresponding full derivatives vanish along
that section. Applying the shifted field preserves these zero lower jets
and acts on the leading jet by the sum of the linearized slot actions. The
scalar multiplier contributes zero to that jet. A uniform power of the
slot sum kills the leading jet, while the eigenvalue raised to the same
power remains nonzero. The distribution therefore kills the original
test, lowering the transverse order. Iterating the descent gives local
vanishing, and a partition of unity gives vanishing on the whole domain.

This internal result applies to the paired stabilizer field and its scalar
correction in the lower real Bruhat charts.
