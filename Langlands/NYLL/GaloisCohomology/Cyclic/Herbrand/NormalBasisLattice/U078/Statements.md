# Integer-ring comparison and principal-unit subgroup existence targets

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.078 | 1494–1502 | `integerRingToFieldLinearMap_range_eq` | `integerRingToFieldLinearMap_range_eqStatement` |
| M144.079 | 1508–1521 | `integerRingFieldSubmodule_fg_of_moduleFinite` | `integerRingFieldSubmodule_fg_of_moduleFiniteStatement` |
| M144.080 | 1526–1536 | `exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLattice` | `exists_chosenBaseUniformizerPow_integerRingFieldSubmodule_le_chosenNormalBasisIntegerLatticeStatement` |
| M144.081 | 1539–1556 | `exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zero` | `exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_mem_nhds_zeroStatement` |
| M144.082 | 1559–1572 | `exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosed` | `exists_chosenBaseUniformizerPow_chosenNormalBasisIntegerLattice_isClosedStatement` |
| M144.083 | 1575–1590 | `exists_chosenNormalBasisPrincipalUnitSet_inv_mem` | `exists_chosenNormalBasisPrincipalUnitSet_inv_memStatement` |
| M144.084 | 1593–1621 | `exists_chosenNormalBasisPrincipalUnitSubgroup` | `exists_chosenNormalBasisPrincipalUnitSubgroupStatement` |

Write `M = chosenNormalBasisIntegerLattice K L`,
`E_n = chosenBaseUniformizerPowSubmodule K L n M`, and
`V_n = chosenNormalBasisPrincipalUnitSet K L n`.

- M144.078 identifies the range of the actual `𝒪[K]`-linear inclusion
  `integerRingToFieldLinearMap K L : 𝒪[L] →ₗ[𝒪[K]] L` with
  `integerRingFieldSubmodule K L`, whose carrier is the valuation integer ring
  viewed inside `L`.
- M144.079 adds `[Module.Finite 𝒪[K] 𝒪[L]]` and states that this concrete
  submodule is finitely generated over `𝒪[K]`.
- M144.080 retains the same module-finiteness assumption and asserts a natural
  number `n` for which the chosen base-uniformizer power of the integer-ring
  submodule is contained in `M`. This is the reverse lattice bound; its
  quantifier is existence of a single level.
- M144.081 adds the original topology and nonarchimedean local-field instances
  on `L`, and asserts one bound `c` such that `E_n` is a neighborhood of zero
  for every `n ≥ c`.
- M144.082, with those same instances, asserts eventual closedness of `E_n`
  as a subset of `L`.
- M144.083 asserts eventual inverse closure of `V_n` under those same instances
  and module-finiteness assumption. There is no separate closedness premise
  in this target.
- M144.084 asserts one bound `c` such that every `n ≥ c` admits a subgroup
  `V : Subgroup 𝒪[L]ˣ` whose carrier is exactly `V_n` and which is contained in
  `principalUnits L 1`. The carrier equality fixes the subgroup to the actual
  normal-basis unit set at that level.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Replace each source theorem by a Prop-valued `def` with the suffix `Statement`,
retaining its proposition verbatim. Omit theorem proofs and theorem attributes.
The effective source section telescope is made explicit before the original theorem binders,
retaining source instance order and source `omit` effects. These are targets, not proofs.

Each declaration starts with explicit `(K L : Type u)` and the following instance binders,
followed in order by exactly its original theorem-specific binders:

- M144.078: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[ValuativeRel K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.079: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[ValuativeRel K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.080: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.081: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.082: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.083: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.
- M144.084: `[Field K]`, `[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`, `[ValuativeRel L]`, `[Valuation.HasExtension (ValuativeRel.valuation K) (ValuativeRel.valuation L)]`.

The source `omit` clauses at lines 1491–1492 and 1504–1505 remove
`FiniteDimensional K L`, `IsGalois K L`, `TopologicalSpace K` and
`IsNonarchimedeanLocalField K` from M144.078 and .079; the reduced telescopes
above retain precisely this effect. M144.079 and .080 then have the original
`[Module.Finite 𝒪[K] 𝒪[L]]` binder. M144.081–.084 instead append
`[TopologicalSpace L] [IsNonarchimedeanLocalField L] [Module.Finite 𝒪[K] 𝒪[L]]`
in that order. M144.078 has none of these extra instances, and .079 and .080
have no topology or local-field instance on `L`. All seven retain the
valuation-extension instance. The U044 linear inclusion and integer-ring
submodule, U059 unit set and existing principal-unit subgroup are imported by
their Lean names.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
