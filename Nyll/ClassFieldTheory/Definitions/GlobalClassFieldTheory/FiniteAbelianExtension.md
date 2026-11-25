# Finite abelian extensions of a number field

Module `Nyll.ClassFieldTheory.Definitions.GlobalClassFieldTheory.FiniteAbelianExtension`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The type of finite abelian extensions of a number field `K`, taken as subfields of Mathlib's chosen separable closure. As the module comment says, the file contains no class field theory.

- `FiniteAbelianExtension K`: the subtype of intermediate fields `E` of `SeparableClosure K` over `K` with `E` finite-dimensional over `K` and abelian Galois (`IsAbelianGalois K E`). Its order is inclusion of intermediate fields.
- Instances: each `E` coerces to a type that is a field, a `K`-algebra, finite-dimensional over `K`, a number field, and abelian Galois over `K`.

## Points to watch

An extension is a subfield of the fixed `SeparableClosure K`, not an abstract extension: two elements are equal exactly when they are the same intermediate field. The coerced type lives in the universe of `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/Definitions/GlobalClassFieldTheory/FiniteAbelianExtension.lean`: the Lean file is the source byte for byte (SHA-256 `932d857f51d0dc939684adeb2129b0c0e420bb151c72fc570efb335b2bd837c6`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
