# Renard II.1.2: disjoint indicators and both exact sequences

Worker 1218 proves the unchanged public
`Langlands.HarmonicAnalysis.TestFunctionDistributionStatements.Assertions.{u}`.
The proof uses the original scalar test functions, characteristic functions,
zero extension, closed restriction, closed pushforward and open restriction.
The distribution spaces are the full complex algebraic duals.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, II.1.2, printed page 31 / PDF
page 37, first unnumbered lemma, proposition (II.1.2.1) and corollary
(II.1.2.2). The conventions on printed page 30 / PDF page 36 identify
test functions as compactly supported locally constant complex functions and
distributions as their algebraic duals, without topologies on those spaces.
Registered source: `renard-2026-representations-groupes-reductifs-padiques`,
SHA256 `7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1218 read these two original pages.

The implemented indicator argument uses the finitely many nonzero values of
the actual function. Local constancy makes each fiber clopen, and every nonzero
fiber is a closed subset of the compact support. Distinct fibers are disjoint.
A finite enumeration supplies the required `Fin n` family. At a zero value
every indicator vanishes; at a nonzero value exactly the corresponding fiber
contributes. This is an alternative to the source's finite compact-open cover
and disjoint refinement.

For the test-function sequence, the published
`SchwartzBruhat.extendZero_injective` supplies injectivity and the published
`SchwartzBruhat.closedRestrictionSurjective` supplies surjectivity. A zero
extension vanishes on the literal closed complement. Conversely, a function
whose closed restriction is zero vanishes outside the open set; the public
`Distribution.FiniteOrbitVanishingProof.exists_extension_eq` supplies its
zero-extension preimage by restricting its compact clopen support to the
subspace. These two implications prove equality of the actual linear-map
range and kernel.

For distributions, the original closed pushforward and open restriction are
definitionally the algebraic dual maps of the two test-function maps.
Mathlib's duality lemmas give injectivity from surjectivity and surjectivity
from injectivity. They identify the range of a dual map with the annihilator
of the original kernel, and its kernel with the annihilator of the original
range. The test-function range-kernel equality therefore proves the dual
range-kernel equality. This implements the source's algebraic duality step
without any finite-dimensionality assumption.

The exact Mathlib results are
`LinearMap.dualMap_injective_of_surjective` and
`LinearMap.ker_dualMap_eq_dualAnnihilator_range` in
`Mathlib/LinearAlgebra/Dual/Defs.lean`, lines 143–148 and 479–483, and
`LinearMap.dualMap_surjective_of_injective` and
`LinearMap.range_dualMap_eq_dualAnnihilator_ker` in
`Mathlib/LinearAlgebra/Dual/Lemmas.lean`, lines 827–835, at pinned Mathlib
commit `5ed2965256430c3649e86755f9576b54eca72435`.
The registered sources are `mathlib-algebraic-dual-defs-5ed296525643`
(SHA256 `db35779a419e6801ac1f44cc73730a1cf38172700d83a38876b26232614805b6`)
and `mathlib-algebraic-dual-lemmas-5ed296525643`
(SHA256 `45f6851df21387799575c2844b7c7b50ffad353a938a4bcfcb6f032f78443902`).
These are invoked as published Mathlib lemmas; no source code is copied.

The aggregate retains the arbitrary universe and supplied topology and
requires only the hypotheses already in the public statement. No
nonemptiness, countability or global compactness assumption is added.
For a zero function the nonzero-value family is empty, so `n = 0` is
allowed; empty spaces and empty or full open subsets are included.

The implementation imports the public statement unchanged. Its three named
theorems prove exactly the three conjuncts; `assertions` packages them in the
public order. Development check `a89d7640-22a5-4215-a2b4-9e75988de354`
compiled the module with zero errors and warnings and inspected the aggregate:
its sole universe parameter is `u`, and its axioms are `propext`,
`Classical.choice` and `Quot.sound`. Independent review and exact-candidate
validation are separate publication requirements.
