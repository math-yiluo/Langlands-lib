# Principal-unit lattice bound targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.063 | 1147–1162 | `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_one` | `chosenNormalBasisPrincipalUnitSet_mem_principalUnits_oneStatement` |
| M144.064 | 1166–1186 | `exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_one` | `exists_chosenNormalBasisPrincipalUnitSet_mul_closed_le_principalUnits_oneStatement` |

Write `M = chosenNormalBasisIntegerLattice K L`,
`E_n = chosenBaseUniformizerPowSubmodule K L n M`, and
`V_n = chosenNormalBasisPrincipalUnitSet K L n`. Thus `V_n` consists of units
of `𝒪[L]` whose deviation from one, coerced into `L`, belongs to the actual
uniformizer-power normal-basis lattice `E_n`.

- M144.063 retains an implicit level `n`, an explicit containment
  `E_n ≤ maximalIdealFieldSubmodule K L`, an implicit unit `u`, and its explicit
  membership proof in `V_n`, in that order. Its target says that `u` belongs to
  `principalUnits L 1`. The comparison object is the image in `L` of the actual
  maximal ideal of `𝒪[L]`.
- M144.064 adds `[TopologicalSpace L] [IsNonarchimedeanLocalField L]` and
  asserts one natural-number bound `c` such that every `n ≥ c` has both
  multiplication closure of `V_n` and inclusion `V_n ⊆ principalUnits L 1`.
  It supplies neither an inverse-closure conclusion nor a subgroup construction.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.063: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.064: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.

Both declarations retain the source valuation-extension instance. M144.063 has
no topology or local-field instance on `L`; the two such instances in M144.064
are original theorem-specific binders after the common telescope. The imported
U059 carrier and U044 maximal-ideal submodule are reused by their Lean names,
as is the existing `LocalFieldTheory.principalUnits` construction.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
