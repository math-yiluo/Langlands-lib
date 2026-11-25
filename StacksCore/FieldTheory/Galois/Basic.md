# The fixed field of a cyclic subgroup of a Galois group

Module `StacksCore.FieldTheory.Galois.Basic`, an extract of the file of the same path of the Lean library AxiomMath/Stacks. The origin of the file and what the extract leaves out are given at the end of this page.

- `IntermediateField.mem_fixedField_zpowers_iff`: for a field extension `K/F`, `σ ∈ Gal(K/F)` and `b ∈ K`, the element `b` lies in the fixed field of the cyclic subgroup `⟨σ⟩` if and only if `σ b = b`.

The proof checks `σⁿ b = b` for every integer `n` by induction on `n`.

## References

No declaration of the file carries a tag. The table of tags below attaches Tags 0BMH and 0BMM to Mathlib's `AlgEquiv.restrictScalars_injective`, `IntermediateField.fixingSubgroupEquiv` and `AlgEquiv.restrictNormalHom_surjective`, and Tag 09I3 to Mathlib's `IsGaloisGroup.fixedPoints`.

## Stacks Project tags

| Tag | Declaration | Note |
| --- | --- | --- |
| [0BMH](https://stacks.math.columbia.edu/tag/0BMH) | `IntermediateField.fixingSubgroupEquiv` | injective |
| [0BMM](https://stacks.math.columbia.edu/tag/0BMM) | `IntermediateField.fixingSubgroupEquiv` | injective |
| [0BMH](https://stacks.math.columbia.edu/tag/0BMH) | `AlgEquiv.restrictScalars_injective` | injective |
| [0BMM](https://stacks.math.columbia.edu/tag/0BMM) | `AlgEquiv.restrictScalars_injective` | injective |
| [0BMH](https://stacks.math.columbia.edu/tag/0BMH) | `AlgEquiv.restrictNormalHom_surjective` | surjective |
| [0BMM](https://stacks.math.columbia.edu/tag/0BMM) | `AlgEquiv.restrictNormalHom_surjective` | surjective |
| [09I3](https://stacks.math.columbia.edu/tag/09I3) | `IsGaloisGroup.fixedPoints` | G is the Galois group |

## Origin of the file

Extracted from the Lean library AxiomMath/Stacks (https://github.com/AxiomMath/Stacks), commit `c496df0d9beea9deaeabcea8492605f9a0a2313b`, file `StacksCore/FieldTheory/Galois/Basic.lean`. That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the extract:

- Of the 9 declarations of the source file 1 are kept. The 8 left out are not needed by the results for which the extract is made: `AlgEquiv.exists_restrictScalars_eq_of_restrictNormal_eq_one`, `AlgEquiv.ker_restrictNormalHom_eq_image_restrictScalarsHom`, `AlgEquiv.restrictNormal_restrictScalars`, `IntermediateField.mem_fixingSubgroup_adjoin_iff`, `IsGalois.fintypeCard_aut_eq_finrank`, `IsGalois.normalClosure'`, `IsGalois.of_isNormalClosure`, `restrictNormal_restrictScalars_aux`.
- The import lines are those that the kept text needs.
- The library's Lean options that differ from Lean's defaults are set at the top of the file (`autoImplicit false`, `maxSynthPendingDepth 3`).
- The import of the library's own attribute modules is replaced by `Mathlib.Tactic.CrossRefAttribute`.
