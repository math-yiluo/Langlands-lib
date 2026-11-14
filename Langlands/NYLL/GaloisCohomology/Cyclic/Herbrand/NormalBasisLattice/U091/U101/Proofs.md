# Equality of representatives in the successor lattice quotient (M144.101)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotMk_eq_iff` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotMk_eq_iffStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The statement says that two representatives in the level-`n` normal-basis
lattice have equal images in the successor quotient if and only if their
difference belongs to `chosenNormalBasisLatticeSuccSubmodule K L n`.
This is the actual submodule of the level-`n` lattice obtained from the
level-`n + 1` lattice by `submoduleOf`.

The proof retains the pinned source argument. After unfolding the target and
the canonical map definitionally with `change`, the equality is an equality
of `Submodule.Quotient.mk` classes in the concrete submodule quotient.
Mathlib's `Submodule.Quotient.eq` gives exactly the difference-membership
criterion, completing both directions of the equivalence.

The sole direct import is the published `U091.Statements` module. Its
`U086.Definitions` dependency supplies the actual quotient and canonical
map; its Mathlib imports supply the quotient equality criterion. No other
NYLL proof is used. As in the original source's explicit `omit` directives
at lines 1840–1841, neither a valuation on `L` nor a valuation-extension
hypothesis is required.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1845–1858.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
