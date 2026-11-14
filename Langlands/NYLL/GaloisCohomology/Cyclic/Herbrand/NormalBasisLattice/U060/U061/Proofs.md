# The identity in the normal-basis principal-unit set (M144.061)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_one_mem`
proves the exact published `chosenNormalBasisPrincipalUnitSet_one_memStatement`
with its full field, Galois, valuation, and local-field parameters and every
natural level. No valuation-extension hypothesis is added.

The implementation unfolds the target and the principal-unit set, simplifies
the image of `1 - 1` to zero, and applies zero membership in the scaled
normal-basis submodule. It imports only `U060.Statements` and its published
transitive dependencies. The source rewrites with M144.060; here that same
definitional membership step is performed by `change`, so the proof does not
depend on an unpublished lemma.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1109–1116.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the direct
unfolding described above. The original copyright/author header and
`licenses/NYLL/LICENSE` (Apache-2.0) and `NOTICE` remain in the Library.
This support result makes no host reciprocity or class-formation claim.
