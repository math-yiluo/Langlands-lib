# Everywhere unramified extensions of number fields

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.NumberField.EverywhereUnramifiedTower`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file defines when an extension of number fields is unramified at all places, finite and infinite, and proves that the notion behaves well in towers.

## Main definitions and results

- `IsEverywhereUnramified K L`: a structure with two fields, `IsUnramifiedAtFinitePlaces K L` (the library's notion, unramified at every finite prime) and Mathlib's `IsUnramifiedAtInfinitePlaces K L` (no real place of `K` becomes complex in `L`).
- `IsEverywhereUnramified.refl`: `K/K` is everywhere unramified.
- For a tower `k ⊆ K ⊆ F` of number fields:
  - `trans`: if `K/k` and `F/K` are everywhere unramified, so is `F/k`;
  - `top`: if `F/k` is, so is `F/K`;
  - `bot`: if `F/k` is, so is `K/k`.

## Proof

Each statement combines the corresponding tower lemma for finite primes from the library with Mathlib's tower lemmas for infinite places.

## Points to watch

- The finite-place half is the library's own definition `IsUnramifiedAtFinitePlaces`, not a Mathlib notion.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/NumberField/EverywhereUnramifiedTower.lean`: the Lean file is the source byte for byte (SHA-256 `bdcb66d21a622d69b1bb110052975792e5226137a2dc9452d37e0c6079d98515`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
