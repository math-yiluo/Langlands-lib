# The left regular distribution action is convolution

This module proves `Langlands.leftRegularCompactDistribution`, whose type is
exactly `Langlands.LeftRegularCompactDistributionStatement`, with the original
group universe and assumptions.

The target comes from David Renard, *Représentations des groupes réductifs
p-adiques*, French edition of 9 July 2026, III.1.3, Example, printed p.59 /
PDF p.65; registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

The implemented proof applies the assumed scalar characterization to the linear
functional evaluating a test function at `x`. Its coefficient is the locally
constant function `g ↦ f(g⁻¹x)`. The test used to define
`Distribution.leftConvolveTest` has these same values everywhere, so
`Distribution.compactSupportFunctional_eq_of_agrees` identifies its evaluation
with the extended compact-support pairing. This proves the formula for any
action satisfying the stated characterization.

The statement module and all of its dependencies remain unchanged.
