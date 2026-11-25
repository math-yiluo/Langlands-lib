# Fixed points of powers of the Frobenius of a finite field

Module `Nyll.SchemeTheory.RingTheory.FieldExtensions.FiniteFrobeniusFixed`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite field `k` and an algebraic extension `Ω` of `k`, the file identifies the subfields of `Ω` cut out by powers of the arithmetic Frobenius `x ↦ x^(|k|)` (Mathlib's `frobeniusAlgEquivOfAlgebraic`).

- `LocalClassFieldTheory.mem_range_algebraMap_iff_frobenius_fixed_in`: an element of `Ω` lies in the image of `k` if and only if Frobenius fixes it. The proof notes that a fixed element is a root of `X^(|k|) − X`, which splits over `k`.
- `FiniteField.mem_range_algebraMap_iff_frobenius_pow_fixed`: for a finite field `E` with `k ⊆ E ⊆ Ω` and `[E : k] = m`, an element of `Ω` lies in the image of `E` if and only if the `m`-th power of the Frobenius of `k` fixes it. It applies the first result over `E` and identifies the Frobenius of `E`, viewed over `k`, with the `m`-th power of that of `k` (`frobeniusAlgEquiv_restrictScalars`).

The second statement concerns a given finite extension `E` embedded in `Ω`; it does not by itself produce, for each `m`, a subfield of `Ω` of degree `m`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/SchemeTheory/RingTheory/FieldExtensions/FiniteFrobeniusFixed.lean`: the Lean file is the source byte for byte (SHA-256 `cfe115816298d6d11365395d9c570091c88e85847e0168a1b2f7097a55c4698c`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
