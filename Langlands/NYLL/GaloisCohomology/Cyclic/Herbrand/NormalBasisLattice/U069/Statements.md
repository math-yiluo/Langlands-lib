# Principal-unit inverse convergence targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.069 | 1265–1282 | `chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zero` | `chosenNormalBasisPrincipalUnitSet_neg_sub_one_pow_succ_tendsto_zeroStatement` |
| M144.071 | 1309–1343 | `chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_one` | `chosenNormalBasisPrincipalUnitSet_inverseCorrectionProduct_tendsto_oneStatement` |
| M144.072 | 1346–1378 | `chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_inv` | `chosenNormalBasisPrincipalUnitSet_one_add_inverseCorrection_tendsto_invStatement` |
| M144.073 | 1381–1395 | `chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_one` | `chosenNormalBasisPrincipalUnitSet_inverseCorrection_tendsto_inv_sub_oneStatement` |
| M144.075 | 1424–1450 | `chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closed` | `chosenNormalBasisPrincipalUnitSet_inverse_sub_one_mem_of_closedStatement` |
| M144.076 | 1453–1470 | `chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed` | `chosenNormalBasisPrincipalUnitSet_inv_mem_of_closedStatement` |
| M144.077 | 1473–1489 | `exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closed` | `exists_chosenNormalBasisPrincipalUnitSet_inv_mem_of_closedStatement` |

Write `M = chosenNormalBasisIntegerLattice K L`,
`E_n = chosenBaseUniformizerPowSubmodule K L n M`, and
`V_n = chosenNormalBasisPrincipalUnitSet K L n`. For a unit `u`, let `x` denote
its deviation from one coerced into `L`. The imported U030 construction
`S_d(x) = inverseCorrectionPartialSum x d` is the finite sum
`(-x) + (-x)^2 + ... + (-x)^d`, with the empty sum at `d = 0`.

- M144.069 retains a containment `E_n ≤ maximalIdealFieldSubmodule K L` and a
  unit `u ∈ V_n`. It states that `(-(u - 1))^(d + 1)` tends to zero as
  `d → ∞`, in the valuation integer ring `𝒪[L]`.
- M144.071, with the same hypotheses, states that the field-valued sequence
  `u * (1 + S_d(x))` tends to `1` in `L`.
- M144.072 states that `1 + S_d(x)` tends to the image of the unit inverse
  `u⁻¹` in `L`. M144.073 states that `S_d(x)` tends to that image minus one.
  All coercions through the valuation integer ring remain in the Lean targets.
- M144.075 assumes, in order, that `E_n` is closed as a subset of `L`, that
  `E_n` lies in the maximal-ideal submodule, and that every product of two
  elements of `E_n` again belongs to `E_n`. For an implicit unit `u` and an
  explicit proof `u ∈ V_n`, its target places the deviation `u⁻¹ - 1` in `E_n`.
- M144.076 retains those same hypotheses and states `u⁻¹ ∈ V_n`.
- M144.077 asserts one natural-number bound `c` such that, for every `n ≥ c`,
  closedness of `E_n` implies inverse closure of `V_n`. Closedness remains an
  implication premise for each level, rather than a conclusion of this target.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.069: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.071: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.072: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.073: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.075: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.076: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.077: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.

Each declaration next retains the original theorem-specific
`[TopologicalSpace L] [IsNonarchimedeanLocalField L]` binders. In M144.069,
.071, .072 and .073 these precede implicit `n`, explicit lattice containment,
implicit `u` and explicit membership. In M144.075 and .076 they precede
implicit `n`, the three explicit lattice hypotheses, implicit `u` and explicit
membership. M144.077 has no further parameter binders. All seven retain the
valuation-extension instance. U059, U030 and U044 supply the actual carrier,
finite correction sum and maximal-ideal comparison submodule by their Lean
names; no replacement object or new instance is introduced here.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
