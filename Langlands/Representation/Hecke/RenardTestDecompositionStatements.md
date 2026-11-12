# Finite coset expansions of scalar test functions

`Langlands.Hecke.RenardTestDecomposition.Statements` is the conjunction of
three closed proposition definitions for the two clauses of the II.3.5
Lemma. No proofs are supplied.

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.3.5 Lemma, printed p.46 /
PDF p.52, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.

All three targets quantify an arbitrary Hausdorff, locally compact,
totally disconnected topological group with its supplied structures.
These are exactly Renard's t.d. hypotheses, by the published
`Langlands.Topology.isLocallyProfinite_iff_mathlib`. There is no countability,
unimodularity or measure assumption.

`DoubleCosetExpansionStatement` asserts that every actual
`SchwartzBruhat G` is a finite complex linear combination of the published
`Hecke.TestFunction.doubleCosetIndicator K hK (g i)`, for one compact open
subgroup `K`. Pairwise disjointness of the actual `K g i K` subsets makes
the finite family a family of representatives of distinct double cosets.
This is the source's part (i), with finite families indexed by `Fin n`.

`LeftInvariantExpansionStatement` and `RightInvariantExpansionStatement`
are the two alternatives of part (ii). The invariance premises use the
published translations and the given compact open subgroup. The support
is exactly a finite union of distinct cosets, and the original scalar
function equals the indicated finite sum of their characteristic
functions. For left invariance these are the right cosets `K g i`; for
right invariance these are the left cosets `g i K`. This preserves the
source's coset conventions. The nonzero-coefficient requirement simply
omits zero terms so that the support equality uses the same family.
The empty family is permitted and represents the zero test.

The Library already contains useful ingredients rather than these exact
three statements: `Hecke.TestFunction.commonCompactOpenBiInvariance`
gives a common compact open subgroup for any finite family of tests, and
`Hecke.HeckeAlgebra.Corner.span_range_doubleCoset` spans the actual
Haar-function corner by normalized double-coset functions. The latter
requires a Haar measure and does not state the one-sided support
expansions. These targets retain the original unnormalized indicators
and the exact original test-function carrier.

The II.3.5 Corollary's common-invariance content already follows directly
from `commonCompactOpenBiInvariance G {f} ⊤`: membership in the actual
bi-invariant submodule is equivalent to fixedness for both source
translations by `mem_biInvariant_iff`. Thus every test belongs to each of
the left, right and two-sided uniform unions. Conversely those test
unions consist of tests by definition. Their embedding into locally
constant functions is the existing subtype inclusion. This direct
correspondence is recorded here to avoid presenting the Corollary as a
new unproved result.
