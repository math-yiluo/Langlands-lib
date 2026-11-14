# The concrete successor-quotient equivalence on representatives (M144.093)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mkStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The chosen lattice quotient is defined as the concrete submodule
quotient. Its concrete linear equivalence is `LinearEquiv.refl`, and its
quotient map is the successor submodule's `mkQ`. Evaluating that equivalence
on the image of a representative is definitionally `Submodule.Quotient.mk x`.
The implemented proof is `rfl`, exactly the source proof, and retains the
simp annotation. It imports only `U091.Statements` and its published
transitive definitions. The target requires no valuation instance on `L`.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1724–1733.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
