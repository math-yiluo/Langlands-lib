# Normal-basis principal-unit set membership (M144.060)

`Langlands.NYLL.CyclicCohomology.mem_chosenNormalBasisPrincipalUnitSet_iff`
proves the exact published
`Langlands.NYLL.CyclicCohomology.mem_chosenNormalBasisPrincipalUnitSet_iffStatement`
for every pair of fields and all instances in that target, every natural level,
and every integer-ring unit. The target does not require a valuation-extension
instance on the two fields.

The set is defined by membership of the image of `u - 1` in the scaled
normal-basis integer lattice. Unfolding this set membership makes the two sides
definitionally equal, so the implemented proof is `Iff.rfl`. It uses the
published definitions through `U060.Statements`, with no additional proof input.

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1100–1108.
Registered source: `nyll-classfieldtheory-fbd320cd-supplement`, content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The upstream reflexivity proof and simp annotation are retained. Worker 642
adapts the namespace/import and types the theorem with the existing Prop target;
no published target or dependency is changed. The upstream copyright and author
header, Apache-2.0 license, and `licenses/NYLL/LICENSE` and `NOTICE` are retained.
This support lemma makes no host reciprocity or class-formation claim.
