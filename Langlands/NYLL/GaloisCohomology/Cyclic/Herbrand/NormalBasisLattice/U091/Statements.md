# Successive lattice quotient representative targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.091 | 1703–1708 | `mem_chosenNormalBasisLatticeSuccSubmodule_iff` | `mem_chosenNormalBasisLatticeSuccSubmodule_iffStatement` |
| M144.093 | 1724–1729 | `chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mk` | `chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv_mkStatement` |
| M144.100 | 1828–1838 | `chosenNormalBasisLatticeSuccQuotMk_eq_zero_iff` | `chosenNormalBasisLatticeSuccQuotMk_eq_zero_iffStatement` |
| M144.101 | 1845–1856 | `chosenNormalBasisLatticeSuccQuotMk_eq_iff` | `chosenNormalBasisLatticeSuccQuotMk_eq_iffStatement` |

Write `E_n` for the chosen uniformizer-power normal-basis lattice. Its
successor denominator is `E_(n+1).submoduleOf E_n`, and the quotient is the actual
`𝒪[K]`-module quotient of `E_n` by that denominator. M144.091 states that a
representative belongs to the denominator exactly when its underlying field
element belongs to `E_(n+1)`. M144.093 identifies the image of a representative
under the concrete equivalence with `Submodule.Quotient.mk`. M144.100 says its
quotient class is zero exactly when that field element is at the next level;
M144.101 says two classes agree exactly when their difference belongs to the
denominator, with subtraction in the subtype `E_n`.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.091: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`.
- M144.093: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`.
- M144.100: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`.
- M144.101: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
