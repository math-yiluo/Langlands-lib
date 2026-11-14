# Successive normal-basis principal-unit sets descend (M144.085)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_succ_subset` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisPrincipalUnitSet_succ_subsetStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The private helper `scaledSucc_le_local` proves successor inclusion of
scaled integer-base submodules. An element at level `n+1` has the form
`π^(n+1) * y` with `y ∈ N`. Scalar closure gives `π * y ∈ N`, and
`pow_succ`, preservation of multiplication by `algebraMap`, and associativity
rewrite the element as `π^n * (π * y)`. This is the required level-`n`
representation.

Applying that helper to the image of `u - 1` proves the public set inclusion.
Membership reduces definitionally, replacing the source's M144.060 rewrite.
The source applies M144.019, which in turn uses M144.018. These proofs are not
published in the workspace base; the private helper adapts their witness
argument at the single successor step (same source, lines 209–230). No
second public copy of either reserved name is introduced. The only import
is `U060.Statements` with its published transitive definitions.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1647–1655.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
