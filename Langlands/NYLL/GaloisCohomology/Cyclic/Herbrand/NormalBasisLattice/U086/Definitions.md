# Successive normal-basis lattice quotient data

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.086 | 1656–1662 | `chosenNormalBasisLatticeSuccSubmodule` | `chosenNormalBasisLatticeSuccSubmodule` |
| M144.087 | 1665–1667 | `chosenNormalBasisLatticeSuccQuot` | `chosenNormalBasisLatticeSuccQuot` |
| M144.088 | 1670–1675 | `chosenNormalBasisLatticeSuccQuotAddCommGroup` | `chosenNormalBasisLatticeSuccQuotAddCommGroup` |
| M144.089 | 1679–1684 | `chosenNormalBasisLatticeSuccQuotModule` | `chosenNormalBasisLatticeSuccQuotModule` |
| M144.090 | 1688–1697 | `chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv` | `chosenNormalBasisLatticeSuccQuotConcreteLinearEquiv` |
| M144.092 | 1711–1718 | `chosenNormalBasisLatticeSuccQuotMk` | `chosenNormalBasisLatticeSuccQuotMk` |

The actual submoduleOf denominator, additive submodule quotient, AddCommGroup and valuation-ring Module instances, concrete identity equivalence and canonical linear quotient map.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Keep the actual source construction bodies, universes and binder kinds.
The effective common telescope is `(K L : Type u)`, `[Field K]`, `[Field L]`,
`[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`,
`[TopologicalSpace K]`, and `[IsNonarchimedeanLocalField K]`, in that order.
Each declaration then takes explicit `(n : Nat)`. Neither `[ValuativeRel L]` nor the
enclosing valuation-extension instance is a parameter of these additive constructions.
The denominator is the successor lattice pulled back to the current lattice by
`Submodule.submoduleOf`; the quotient is the actual `Submodule` quotient.
The two instances preserve source global scope and infer the structures of this
new quotient wrapper. The concrete linear equivalence is `LinearEquiv.refl`, and
the quotient map is the denominator's canonical `mkQ`.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
