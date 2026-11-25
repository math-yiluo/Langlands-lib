# The field fixed by inertia

Module `FontaineWintenberger.Ramification.Fields.Inertia`, copied from the Lean library FontaineWintenberger. The origin of the file and the changes made in the copy are given at the end of this page.

Let `K` be a complete discretely valued field (in the library's sense) with perfect residue field, `L/K` a finite Galois extension with group `G`, `B = spectralIntegerRing K L`, `I` the zeroth lower ramification group, `U` its fixed field, and `A` the valuation ring of `U` for the restricted spectral valuation. The file shows that `U/K` is unramified and `L/U` totally ramified.

- `inertia_fixedField_ramificationIdx`: the ramification index of `A` over `𝒪[K]` is `1`.
- `inertia_fixedField_top_ramificationIdx`: the ramification index of `B` over `A` is `Nat.card I`.
- `inertia_fixedField_top_ramificationIdx_eq_finrank`, `inertia_fixedField_top_ramificationIdx_eq_field_finrank`: this index equals `Module.finrank A B` and `Module.finrank U L`.
- `inertia_fixedField_residue_surjective`: the map of residue fields from `A` to `B` is surjective.
- `inertiaFixedFieldResidueEquiv`: the resulting isomorphism of residue fields, as algebras over the residue field of `K`.

The proofs use `fixedField_ramificationIdx_eq_relIndex` and other results on fixed fields proved elsewhere.

## What to watch for

"Unramified" appears only as ramification index `1`; separability of the residue extension is not restated here.

## References

Serre, *Local Fields*, Chapter IV.

## Origin of the file

Copied from the Lean library FontaineWintenberger (https://github.com/YijunYuan/FontaineWintenberger), commit `e835d58871d8d564901c0f13b685034cd202659e`, file `FontaineWintenberger/Ramification/Fields/Inertia.lean` (SHA-256 of the source file `f82152d3f16470fc0eb8d0444a42b3e55509f34a58ec59146e1a76a78f2feee9`). That library is distributed under the Apache License, Version 2.0; its licence text is kept with the Library's licences.

Changes made in the copy:

- The two Lean options that the library's lakefile sets and that differ from Lean's defaults are set after the imports (`relaxedAutoImplicit false`, `maxSynthPendingDepth 3`).
