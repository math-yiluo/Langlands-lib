# Injectivity at finite levels of the rational idele-class direct limit

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.Reciprocity.IdeleClassDirectLimitFiniteLevel`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves that scalar extension of relative idele classes between finite rational intermediate fields is injective, and hence that every finite Galois level maps injectively into the direct limit `rationalIdeleClassDirectLimit`. The tool is a comparison of scalar extension with the tower presentation `ℚ ⊆ K ⊆ N`.

## Main results

For intermediate fields `K ≤ N` of `ℚˢᵉᵖ/ℚ`, both finite over `ℚ`, with `N` a `K`-algebra through the inclusion:

- `rationalRelativeAdeleEmbedding_unflatten`: unflattening (`towerRelativeAdeleUnflatten ℚ K N`) the scalar extension of a relative adele `a` of `K` gives `a ⊗ 1`.
- `rationalRelativeIdeleEmbedding_unflatten`: the corresponding statement for relative ideles, with `includeLeft` on units.
- `rationalRelativeIdeleClassEmbedding_towerBaseChange`: the tower base-change equivalence sends the scalar extension of a class `c` to `RelativeIdeleGroup.classInclusion K N` applied to the image of `c` in `C_K`.
- `rationalRelativeIdeleClassEmbedding_injective`: scalar extension `RelativeIdeleGroup.ClassGroup ℚ K → RelativeIdeleGroup.ClassGroup ℚ N` is injective.
- `rationalRelativeIdeleClassToDirectLimit_injective`: for a finite Galois `E`, the canonical map from level `E` to the direct limit is injective.

## Proofs

Injectivity of scalar extension follows from the commuting square of the third result, the injectivity of `classInclusion K N` (an imported lemma, `C_K → C_N`) and the base-change equivalence. Injectivity into the limit is Mathlib's `DirectLimit.mk_injective` applied to injective transition maps.

## Points to watch

- `N` need not be Galois over `K` for injectivity of scalar extension; only finite dimensionality is used.
- The key input, injectivity of `C_K → C_N`, is not proved in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/Reciprocity/IdeleClassDirectLimitFiniteLevel.lean`: the Lean file is the source byte for byte (SHA-256 `3abb6feb0cfa66a4b224461031b26f7f107f1a660b277b5edd17c33c217f5c32`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
