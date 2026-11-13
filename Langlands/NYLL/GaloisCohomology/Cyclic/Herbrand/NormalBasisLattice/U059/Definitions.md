# Normal-basis principal-unit carrier

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.059 | 1092–1094 | `chosenNormalBasisPrincipalUnitSet` | `chosenNormalBasisPrincipalUnitSet` |

The actual set of valuation-ring units whose deviation from one lies in the chosen uniformizer-power normal-basis lattice.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Keep the actual source construction bodies, universes and binder kinds.
The effective common telescope is `(K L : Type u)`, `[Field K]`, `[Field L]`,
`[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`, `[ValuativeRel K]`,
`[TopologicalSpace K]`, and `[IsNonarchimedeanLocalField K]`, in that order.
This is followed by `[ValuativeRel L]` and explicit `(n : Nat)`. The enclosing source
valuation-extension instance is unused and is not a parameter of this definition.
The set uses the literal coercion from a valuation-ring unit to the valuation ring,
subtracts one there, then coerces to `L` for lattice membership. It adds no instance.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
