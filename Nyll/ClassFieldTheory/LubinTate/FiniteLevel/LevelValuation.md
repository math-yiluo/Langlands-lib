# Uniqueness of the valuation on standard Lubin–Tate levels

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.LevelValuation`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` and `π` a uniformizer. The standard Lubin–Tate level `L_n` carries a complete discrete valuation chosen from the integral closure of the valuation ring of `F`. Since `L_n/K` is finite and Galois, this valuation is the only extension of the base valuation.

- `standardLubinTateLevelCompleteDVF_hasUniqueValuationExtension`: the chosen valuation on `L_n` is the unique extension of the valuation of `F`, in the library's sense `HasUniqueValuationExtension`.
- `standardLubinTateLevelCompleteDVF_hasUniqueDVFValuationExtension`: the same statement for the underlying discrete valuation fields, the form used by the library's real-indexed lower and upper ramification groups.

Both follow from the general uniqueness of valuation extensions from a complete base to a finite separable extension, applied with the facts that `L_n/K` is finite-dimensional and Galois.

The uniqueness predicate is the library's own notion, not a Mathlib one. It is instantiated at universe levels `.{u, v, u, 0, 0}`: the chosen valuation is equivalent to every extension of the base valuation whose value group lies in `Type 0`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/LevelValuation.lean`: the Lean file is the source byte for byte (SHA-256 `d9881bec5eecc51c759a59f2c9f87ffadc8271571cdd1a48bdcbf02453ee67a7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
