# Flatness over a fixed base after tensoring

Module `StacksFrontier.RingTheory.Flat.BaseChangeAlongFlatAlgebra`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

For a tower of commutative algebras R → S → S′ and an S-module M, the file compares flatness over R before and after extension of scalars to S′.

- `Module.Flat.stacks_tensorProduct_of_flat` shows that if S′ is S-flat and M is R-flat, then S′ ⊗ M over S is R-flat. This part works over commutative semirings.
- `Module.Flat.tensorProduct_iff_of_faithfullyFlat` gives equivalence of the two R-flatness conditions when S′ is faithfully flat over S. This part is stated for commutative rings.

Tensor associativity identifies tensoring an R-linear map with the extended module with tensoring first by M and then by S′. Flatness preserves injectivity at each step, and faithful flatness reflects it at the last step.

The two results are parts (1) and (2) of Tag 0584. Ascent also cites EGA 0 6.2.1. The module docstring lists part (1) under a different name; in the file it is `Module.Flat.stacks_tensorProduct_of_flat`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0584](https://stacks.math.columbia.edu/tag/0584) | `stacks_tensorProduct_of_flat` | (1) |
| [0584](https://stacks.math.columbia.edu/tag/0584) | `tensorProduct_iff_of_faithfullyFlat` | (2) |

## References to EGA and SGA

| Source | Place | Declaration | Note |
| --- | --- | --- | --- |
| EGA | 0 6.2.1 | `stacks_tensorProduct_of_flat` | M⊗_A N is B-flat |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksFrontier/RingTheory/Flat/BaseChangeAlongFlatAlgebra.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Every declaration of the source file is kept.
- Renamed, the source's name being declared elsewhere as well (`licenses/Stacks/STX-RENAMES.tsv.md`): `Module.Flat.tensorProduct_of_flat` is `Module.Flat.stacks_tensorProduct_of_flat` here.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
- One reference to EGA or SGA, written in the source as an attribute of that library, is taken out of the Lean text and listed above.
