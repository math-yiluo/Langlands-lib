# Principal-unit additive lattice class

This file adapts NYLL `Nyll/GaloisCohomology/Cyclic/Herbrand/NormalBasisLattice.lean`
at commit `fbd320cd8b1b06487c58227e92eb135794267709`, registered as
`nyll-classfieldtheory-fbd320cd-supplement`, fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.
The retained source root is `/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.
Original copyright and author attribution remain in the Lean header; Apache-2.0 LICENSE and NOTICE
remain in `licenses/NYLL/`. Adaptation: Worker 232.

| Unit | Exact source lines | Source name in `CyclicCohomology` | Adapted name in `Langlands.NYLL.CyclicCohomology` |
| --- | --- | --- | --- |
| M144.102 | 1859–1863 | `chosenNormalBasisPrincipalUnitLatticeClass` | `chosenNormalBasisPrincipalUnitLatticeClass` |

For a natural number `n`, a valuation-ring unit `u` and a supplied proof `hu`
that `u` belongs to the chosen principal-unit set, form `u - 1` in `𝒪[L]` and
coerce it into `L`. The proof `hu` makes this an element of the current power
lattice. Applying `chosenNormalBasisLatticeSuccQuotMk K L n` gives its class in
the actual additive quotient by the successor power lattice. The subtype value
and its proof field, and the quotient-map application, are retained literally.

The effective telescope is explicit `(K L : Type u)`, followed by `[Field K]`,
`[Field L]`, `[Algebra K L]`, `[FiniteDimensional K L]`, `[IsGalois K L]`,
`[ValuativeRel K]`, `[TopologicalSpace K]`, `[IsNonarchimedeanLocalField K]`,
`[ValuativeRel L]`, then `(n : Nat)`, `(u : 𝒪[L]ˣ)` and the explicit membership
proof `hu`, in that order. The enclosing valuation-extension instance is unused
and does not enter this definition. No instance is introduced in this file.

Modifications: prepend `Langlands.NYLL` to the namespace, extract only the listed units,
replace broad source imports with focused Library and Mathlib imports, and place the source
descriptions in this paired Markdown. Keep the actual source construction bodies, universes and binder kinds.
Unused source section instances are not parameters of the data definitions.

The carrier, lattices and quotients are the actual objects in the displayed Lean declarations.
No uniformizer-independence, residue-field scalar action, or host reciprocity/class-formation
conclusion is added. The separate statement targets remain proof obligations.
