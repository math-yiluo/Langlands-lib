# Principal-unit carrier membership and closure targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.060 | 1100–1104 | `mem_chosenNormalBasisPrincipalUnitSet_iff` | `mem_chosenNormalBasisPrincipalUnitSet_iffStatement` |
| M144.061 | 1109–1112 | `chosenNormalBasisPrincipalUnitSet_one_mem` | `chosenNormalBasisPrincipalUnitSet_one_memStatement` |
| M144.062 | 1117–1144 | `chosenNormalBasisPrincipalUnitSet_mul_mem` | `chosenNormalBasisPrincipalUnitSet_mul_memStatement` |
| M144.065 | 1191–1201 | `chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_mem` | `chosenNormalBasisPrincipalUnitSet_inverseCorrectionPartialSum_memStatement` |
| M144.085 | 1647–1653 | `chosenNormalBasisPrincipalUnitSet_succ_subset` | `chosenNormalBasisPrincipalUnitSet_succ_subsetStatement` |

Write `M` for the chosen normal-basis integer lattice, `E_n` for
`chosenBaseUniformizerPowSubmodule K L n M`, and `V_n` for the set of
valuation-ring units whose difference from one, coerced into `L`, lies in `E_n`.
M144.060 unfolds this membership condition, and M144.061 asserts `1 ∈ V_n`.
M144.062 retains the supplied hypothesis that `E_n` is closed under products and
then asserts `u * v ∈ V_n` for supplied members `u` and `v`. Under the same
product-closure hypothesis, M144.065 asserts that every inverse-correction partial
sum of `u - 1` lies in `E_n`. M144.085 states `V_(n+1) ⊆ V_n`.
All differences are formed in the valuation ring before coercion to the field.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.060: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.061: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.062: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.065: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.085: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
