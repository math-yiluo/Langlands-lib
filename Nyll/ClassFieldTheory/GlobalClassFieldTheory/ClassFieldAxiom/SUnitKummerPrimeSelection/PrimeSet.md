# The prime set T of the S-unit Kummer selection

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.SUnitKummerPrimeSelection.PrimeSet`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

In the S-unit Kummer prime selection (K a number field with a primitive n-th root of unity, `n = p^v` with p prime and v > 0, E/K finite abelian inside a separable closure with `Gal(E/K) ≅ (ℤ/n)^r`, S a finite set of finite places), the file packages the chosen base places as a finite set of places of K.

- `sUnitKummerPrimeSet … S`: the set T, the image of the injective family `sUnitKummerChosenBasePlaces`.
- `sUnitKummerPrimeSet_card`: T has `sUnitKummerPrimeCount` elements, the count described in the comments as `s − r`.
- `sUnitKummerPrimeSet_disjoint_enlargeByFiniteKummerRadicalSupport`: T is disjoint from the enlarged set `S'`, since the chosen places avoid it.

## Points to watch

- T rests on a noncanonical choice (`Classical.choose`) of base places, so later statements about T concern this particular set. K and the separable closure must lie in `Type`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/SUnitKummerPrimeSelection/PrimeSet.lean`: the Lean file is the source byte for byte (SHA-256 `5d245187e20ed9d6eb65401c053992f6d96c69fc8dccb8f10f7c43f50997481c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
