# Finite modules across ring isomorphisms

Module `StacksCore.RingTheory.Finiteness.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

The file adds transfer results for Mathlib's `Module.Finite`, finite generation of modules, along ring isomorphisms.

- `Module.Finite.of_equiv_equiv'`: if `B₁` is finite over `A₁`, and ring isomorphisms `A₁ ≃ A₂`, `B₁ ≃ B₂` commute with the algebra maps, then `B₂` is finite over `A₂`. The `A`'s are commutative semirings; its comment says it replaces an unneeded commutativity assumption on `B₁` by `Semiring B₁`.
- `Module.finite_iff_of_equiv_equiv`: the same as an equivalence.

Stacks tags: no declaration of the file carries one; the table below attaches Tag 0560 to Mathlib's `Module.Finite.of_restrictScalars_finite` and Tag 00GL to Mathlib's `RingHom.Finite.comp`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0560](https://stacks.math.columbia.edu/tag/0560) | `Module.Finite.of_restrictScalars_finite` |  |
| [00GL](https://stacks.math.columbia.edu/tag/00GL) | `RingHom.Finite.comp` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/RingTheory/Finiteness/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 4 declarations of the source file 2 are kept. The 2 left out are not needed by the results for which the extract is made: `Module.Finite.iff_scalarTower`, `Module.finite_of_matrix`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
