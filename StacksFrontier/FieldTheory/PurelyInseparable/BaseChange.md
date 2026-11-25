# Purely inseparable base change to separability

Module `StacksFrontier.FieldTheory.PurelyInseparable.BaseChange`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

Inside a perfect field Ω containing a finitely generated field extension K/k, a finite purely inseparable enlargement k′ of the base makes the compositum K′ = k′K separable over k′, and K′ is the reduction of k′ ⊗[k] K.

## The compositum and reduced tensor product

`exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType` assumes a tower k ⟶ K ⟶ Ω with Ω perfect and K/k essentially of finite type. It gives K′ ⊆ Ω over K and k′ ⊆ K′ over k, each finite purely inseparable over the indicated base. It makes K′ the compositum of K and k′, with `Algebra.StacksIsSeparableExtension k′ K′`. The canonical multiplication map k′ ⊗[k] K ⟶ K′ is surjective with kernel the nilradical, identifying K′ with the reduction. The theorem is proved by `Stacks.FieldTheory.SeparableBaseChange.solution`, which has the same statement.

The proof starts from a separably generated square in Ω, given by `exists_isPurelyInseparable_and_isSeparablyGenerated_of_essFiniteType` of `StacksFrontier.FieldTheory.TranscendentalSeparable`, and restricts its top field to the compositum. For the kernel calculation, a sufficiently high Frobenius power of any tensor comes from K, whose map to K′ is injective.

The theorem expresses finite generation as a field by `Algebra.EssFiniteType`. Its separability predicate is this library's own (the docstrings write it `Algebra.IsSeparableExtension`): it allows transcendental extensions and requires a separating transcendence basis in every finitely generated intermediate field.

The module docstring also lists a definition of such squares and their existence for every finitely generated extension (Tag 04KM); neither is in the file.

The references are Tag 030R and EGA 0 19.6.6 for the compositum result, and Tag 030O for the separability terminology.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [030R](https://stacks.math.columbia.edu/tag/030R) | `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType` |  |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 19.6.6 | `exists_isPurelyInseparable_and_isSeparableExtension_of_essFiniteType` |  |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/FieldTheory/PurelyInseparable/BaseChange.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 24 declarations of the source file 8 are kept. The 16 left out are not needed by the results for which the extract is made; `licenses/Stacks/STX-MANIFEST.tsv.md` lists them.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
