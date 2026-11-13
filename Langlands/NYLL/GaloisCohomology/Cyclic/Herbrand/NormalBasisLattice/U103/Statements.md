# Principal-unit multiplicative comparison targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.103 | 1869–1875 | `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iff` | `chosenNormalBasisPrincipalUnitLatticeClass_eq_zero_iffStatement` |
| M144.104 | 1881–1916 | `chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ` | `chosenNormalBasisPrincipalUnitSet_mul_error_mem_succStatement` |
| M144.105 | 1922–1937 | `exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succ` | `exists_chosenNormalBasisPrincipalUnitSet_mul_error_mem_succStatement` |
| M144.106 | 1942–1967 | `chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_add` | `chosenNormalBasisPrincipalUnitLatticeClass_mul_eq_addStatement` |
| M144.107 | 1970–1992 | `exists_chosenNormalBasisPrincipalUnitSubgroupSuccPair` | `exists_chosenNormalBasisPrincipalUnitSubgroupSuccPairStatement` |

Write `E_n` for the chosen uniformizer-power normal-basis lattice and `V_n`
for the unit set defined by membership of `u - 1` in `E_n`. M144.103 states that
the additive class of a supplied member of `V_n` vanishes exactly when it belongs
to `V_(n+1)`. M144.104 retains a supplied hypothesis `E_n * E_n ⊆ E_(n+1)` and
places the error `(uv - 1) - ((u - 1) + (v - 1))` in `E_(n+1)`. M144.105
asserts that this error condition holds for every sufficiently large level,
uniformly for members of `V_n`. M144.106 retains the error condition and the
three explicit membership proofs for `u`, `v` and `uv`, and asserts that the
class of `uv - 1` is the sum of the two classes.

M144.107 additionally takes `[TopologicalSpace L]`,
`[IsNonarchimedeanLocalField L]` and `[Module.Finite 𝒪[K] 𝒪[L]]`, in that order,
after the section instances listed below. It asserts that, at every sufficiently
large level, there exist subgroups with carriers exactly `V_n` and `V_(n+1)`,
with the latter contained in the former and the former contained in
`principalUnits L 1`.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.103: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.104: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.105: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.106: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`.
- M144.107: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
