# Zero representatives in the successor lattice quotient (M144.100)

`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff` proves the exact published
`Langlands.NYLL.CyclicCohomology.chosenNormalBasisLatticeSuccQuotMk_eq_zero_iffStatement`
with every parameter and hypothesis of that target. No additional
valuation-extension hypothesis is introduced.

The implemented proof unfolds the chosen quotient map into the
canonical submodule quotient constructor using `change`. Mathlib's
`Submodule.Quotient.mk_eq_zero` identifies its zero fiber with membership in
the successor submodule. That membership reduces definitionally to membership
of the underlying field element in the level-`n+1` scaled lattice, closing
the goal by `rfl`. This is the source proof, with the published Prop target
as theorem type. It imports only `U091.Statements` and its published
transitive definitions and Mathlib quotient API; it uses no additional NYLL
proof. The target has no valuation instance on `L`.

Adapted by Worker 642 from Naganori Yamaguchi,
`n-yamaguchi-0729/ClassFieldTheory` at commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`, lines 1828–1844.
Registered source `nyll-classfieldtheory-fbd320cd-supplement` has content fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
Changes are the namespace/import, existing Prop target annotation, and the proof
adaptations described above. The original copyright and author header,
`licenses/NYLL/LICENSE` (Apache-2.0), and `NOTICE` are retained.
No published target or imported definition is edited. This support theorem makes
no host reciprocity or class-formation claim.
