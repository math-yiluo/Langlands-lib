# Completions of fields with an absolute value

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.Completion`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a real-valued absolute value `vK` on a field `K`, the file equips Mathlib's completion `vK.Completion` with an absolute value and the dense embedding of `K`. It maps completions along an exact extension `wL` of `vK`, and proves the universal property for maps into complete fields.

## The completion of one field

- `completionAbsoluteValue vK`: the norm of `vK.Completion` as an absolute value. It agrees with `vK` on `K` (`completionAbsoluteValue_coe`), and it induces the completion uniformity (`completionAbsoluteValue_uniformSpace_eq`).
- Properties of `completionAbsoluteValue vK`:
  - `completionAbsoluteValue_complete`: the completion is complete for it;
  - `_isNontrivial`: it is nontrivial when `vK` is;
  - `_isNonarchimedean`: it is nonarchimedean when `vK` is;
  - `completionAbsoluteValue_range_eq`: for nonarchimedean `vK`, it takes the same values as `vK`.
- `toCompletion vK`: the embedding `K → vK.Completion`. It equals the algebra map, and `denseRange_toCompletion` says that it has dense image.

## Completions along an extension

All of these except `extensionCompletionAlgebra` and `toCompletionAlgHom`, which use only `wL`, assume `hw : Extends vK wL`, that is `wL ∘ algebraMap = vK`.

- `completionMap vK wL hw`: the ring map `K̂ → L̂` extending `K → L`. It is an isometry (`completionMap_isometry`) and agrees with `K → L` on `K` (`completionMap_coe`).
- `completionAlgebra`: the algebra structure of `L̂` over `K̂` given by `completionMap`. `extensionCompletionAlgebra`: the algebra structure of `L̂` over `K`. `toCompletionAlgHom`: the embedding `L → L̂` as a `K`-algebra map.
- `completion_isScalarTower`: the tower `K → K̂ → L̂` commutes.
- `completionAbsoluteValue_extends`: the absolute value of `L̂` restricts exactly to that of `K̂`.

## Maps into complete fields

Let `i : K → D` be a ring map into a field `D`, complete for `vD`, with `vD(i x) = vK(x)`.

- `completionMapToCompleteTarget vK vD i hi`: the extension `K̂ → D`. It is an isometry and agrees with `i` on `K`.
- `completionMapToCompleteTarget_eq_of_coe_eq`: it is the only continuous ring map with that property.
- Tower versions, `completionMapToCompleteTarget_comp_completionMap_coe` and `…_comp_completionMap_eq_of_coe_eq`, handle the composite `K̂ → L̂ → D`.

The extensions are built with `UniformSpace.Completion.extensionHom`. Uniqueness uses density and closedness of the equalizer.

## Points to watch

- `completionAlgebra` and `extensionCompletionAlgebra` are reducible definitions, not global instances. They must be introduced locally, as the statements do with `let`.
- Here "nonarchimedean" is Mathlib's `IsNonarchimedean`, not the library's `NonarchimedeanAbsoluteValue`.
- Completeness of the target is the instance `CompleteSpace (WithAbs vD)`, not the library's predicate `IsCompleteForAbsoluteValue`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/Completion.lean`: the Lean file is the source byte for byte (SHA-256 `15b632f75946a29a53db5a4f0d639db7dde5ef06fed75360628c3a716adffaf5`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
