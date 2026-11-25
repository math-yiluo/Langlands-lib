# Valuations of Lubin–Tate iterates at a primitive point

Module `Nyll.ClassFieldTheory.LubinTate.FiniteLevel.CompletedIterates`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a local field structure on `K` with residue field of cardinality `q`, `π` a uniformizer, and `f(y) = y^q + πy` the standard Lubin–Tate polynomial. In the complete valuation ring of the standard finite level `n` (degree `(q − 1)·q^n` over `F`), the file computes the valuation of the iterates `f^(i)` evaluated at the chosen primitive point `λ`.

## Main definitions and results

- `standardLubinTatePrimitivePointIterateInteger hπ n i`: the value `f^(i)(λ)` in the valuation ring of the level. For `i = 0` it is `λ` itself, and `f^(i+1)(λ) = f^(i)(λ)^q + π·f^(i)(λ)` (`standardLubinTatePrimitivePointIterateInteger_succ`).
- `standardLubinTatePrimitivePointIterateInteger_addVal`: for `i ≤ n`, the normalized additive valuation of `f^(i)(λ)` is exactly `q^i`.

## Proof

Induction on `i`, starting from valuation `1` for `λ`, a uniformizer of the level. In `f^(i)(λ)^q + π·f^(i)(λ)` the first term has valuation `q^(i+1)` and the second `(q − 1)·q^n + q^i`, using that the image of `π` has valuation equal to the level degree. For `i + 1 ≤ n` the first is strictly smaller, so the valuation of the sum is the minimum.

## Points to watch

- The result is restricted to `i ≤ n`; the iterates beyond that range are not treated here.
- The iterates are of the specific polynomial `y^q + πy`, not of an arbitrary Lubin–Tate series.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LubinTate/FiniteLevel/CompletedIterates.lean`: the Lean file is the source byte for byte (SHA-256 `4a368fb35670d616fd3d59da2e4a0e0855ff67c97f0b1b4fec3562a015c0373c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
