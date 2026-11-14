# Membership in the successor lattice submodule (M144.091)

`Langlands.NYLL.CyclicCohomology.mem_chosenNormalBasisLatticeSuccSubmodule_iff` proves the exact published
`Langlands.NYLL.CyclicCohomology.mem_chosenNormalBasisLatticeSuccSubmodule_iffStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The successor submodule is the level-`n+1` scaled lattice pulled back
along the subtype inclusion of the level-`n` lattice (`Submodule.submoduleOf`).
Consequently membership of `x` in that submodule is definitionally membership
of its field value at the next level. The proof is `Iff.rfl`, retaining the
source simp annotation. The sole import is `U091.Statements` with its published
definitions; the proof uses no other NYLL theorem. The target has no valuation
instance on `L`.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1703–1710.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
