# A common valued field for an original and a changed Lubin–Tate level

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.ChangedLevelCompositum`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure (`LocalField`) on a field `K`, `π` a uniformizer, `u` a unit of the valuation ring and `n ∈ ℕ`. The standard Lubin–Tate level `n` for `π` and the standard level `n` for the changed uniformizer `uπ` are both intermediate fields of the fixed separable closure of `K`. This file takes their compositum `M` as a common overfield, equips it with a complete discrete valuation, and compares the valuations of the two levels inside it.

## Main definitions and results

- `standardLubinTateChangedLevelCompositumField`: the compositum `M` of the two levels. It is finite-dimensional, separable and Galois over `K`.
- `standardLubinTateChangedLevelCompositumCompleteDVF`: a complete discrete valuation on `M`, chosen (by `Classical.choose`) so that it extends the base valuation, its valuation ring is the integral closure of the base valuation ring, and the fundamental identity `degree = e · f` holds. Since the base is complete, it is the unique extension of the base valuation.
- `standardLubinTateLevelToChangedLevelCompositum`, `standardLubinTateChangedLevelToCompositum`: the inclusions of the two levels into `M`, which are the identity on elements of the separable closure; in particular they send the chosen primitive generators to the chosen primitive Lubin–Tate roots.
- `standardLubinTateLevelToChangedLevelCompositum_hasExtension` and its changed counterpart: the valuation on `M` extends the chosen valuation on each level. Hence each inclusion preserves the conditions `v(x) ≤ 1` and `v(x) < 1` (the `_val_le_one_iff`, `_val_lt_one_iff` lemmas).
- For each level, its ramification index `e` in `M` and the induced map of valuation rings; along this map the normalized additive valuation is multiplied by `e`, and the `r`-th power of the maximal ideal goes into the `(e·r)`-th power.
- `standardLubinTateLevelToChangedLevelCompositumRamificationIndex_eq`: the two levels have the same ramification index in `M`.

## Proof

Extension of valuations follows from uniqueness of the extension of the base valuation to each level. For the equality of ramification indices, the image of the base uniformizer `π` has additive valuation `(q − 1)·q^n` in both levels (`q` the residue field cardinality), its two images in `M` coincide, and the positive factor `(q − 1)·q^n` is cancelled.

## Points to watch

- The valuation on `M` is a choice made through an existence statement; only its listed properties are available.
- No equality between the two levels, and no condition on `u` such as lying in a group of higher units, is assumed.
- Uniqueness is the library's predicate `HasUniqueValuationExtension`, instantiated at universe levels `.{u, v, u, 0, 0}`: every valuation on `M` that extends the base valuation and has its value group in `Type 0` is equivalent to the chosen one.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/ChangedLevelCompositum.lean`: the Lean file is the source byte for byte (SHA-256 `12327cb0f965706be4cbd1cae7b019bc28cefdcffc39e142e4b1c10871da0deb`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
