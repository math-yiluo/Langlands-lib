# Renard II.3.12: uniform density range and discrete exceptions

This unit states five closed propositions and their conjunction, without proofs,
in `Langlands.HarmonicAnalysis.Distribution.RenardUniformDensity`.
Every space, map, action and product is already published: the actual scalar
tests, full algebraic dual, compact-support and uniform-invariance spaces,
`testDensity`, compact distribution convolution and Haar `HeckeAlgebra μ`.

Source: David Renard, *Représentations des groupes réductifs p-adiques*, French
version of 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Locators: II.3.12 Lemma, printed pp.51–52 / PDF pp.57–58; following Dirac
paragraph and Remarks 1–2, printed p.52 / PDF p.58; inversion in the Proposition,
printed p.52 / PDF p.58, together with II.3.7 Proposition (ii), printed p.47 /
PDF p.53, for its modular function realization.

`UniformRangeStatement` is the Lemma's actual density isomorphism: injectivity
of `testDensity μ`, equality of its range with uniformly left-invariant compact
distributions, and equality of that space with its right- and both-invariant
versions. The uniform sets are the published literal unions over compact open
subgroups. Thus a linear equivalence with the range follows, without assuming
an abstract function/distribution correspondence in place of the source map.

`DiracMembershipStatement` corrects the printed unconditional exclusion of
`δ_g` from H(G). It states the exact criterion: the actual Dirac lies in the
test-density range if and only if the supplied group topology is discrete.
For a discrete group a singleton is compact open, and the indicator of `{g}`
divided by its positive Haar mass is a test density for `δ_g`. Conversely, a
Dirac in a uniformly invariant compact-distribution space forces the trivial
subgroup to be open. The printed claim is therefore valid under the added
nondiscrete hypothesis, and false for every discrete group.

`UnitCriterionStatement` similarly corrects Remark 1: the **existing** function
Hecke algebra has a two-sided convolution identity exactly when the group is
discrete. The proposition is an existence criterion for an element satisfying
the two unit laws; no conflicting `One` or unital ring instance is installed.
For a discrete group the normalized identity-point indicator is that unit.
The source's assertion of nonunitality is retained only for nondiscrete groups.

`IdealStatement` expresses Remark 2 directly on the density range and the
original compact convolution. A compact-distribution subtype witness must
coerce to the given range element, and both products must again lie in that
same range. This does not silently assert an operation on a replacement algebra.

`InversionDensityStatement` specifies the unique possible test function
`g(x)=δ_G(x)⁻¹ f(x⁻¹)` by pointwise equality and identifies its actual density
with inversion of `f μ`. The source Proposition preserves H(G); its expression
relative to the same left Haar measure follows from II.3.7 Proposition (ii).
This explicit derived bridge retains the modular factor for nonunimodular
groups. Existing `Hecke.AntiPullback` statements under measure-preserving or
unimodular assumptions do not replace it. The distribution anti-multiplication
law and the normalized compact-open idempotent identities remain separate
obligations.

All five targets retain arbitrary Hausdorff locally compact totally disconnected
groups and any Borel left Haar measure. They assume no second countability,
compactness, discreteness or unimodularity.
