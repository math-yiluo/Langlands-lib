# The index of n-th powers at a finite place

Module `Nyll.ClassFieldTheory.GlobalClassFieldTheory.ClassFieldAxiom.IdeleClassPowerLocalUnitQuotient.FinitePlacePowerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, a finite place v with completion `K_v`, residue characteristic p and local degree `d = [K_v : ℚ_p]`, the file computes the index of the n-th powers in `K_vˣ` when K contains the n-th roots of unity, and identifies the factor `p^(d · v_p(n))` of that index with the norm of the v-part of the ideal `(n)`.

## Main results

- `card_finitePlace_nthPowerQuotient`: if K has a primitive n-th root of unity, then `#(K_vˣ / (K_vˣ)ⁿ) = n · n · p^(d · v_p(n))`. One factor n accounts for the uniformizer direction, the other for the n-th roots of unity.
- `finitePlaceNthPowerDefect n v`: the natural number `p^(d · v_p(n))`.
- `finitePlaceNthPowerDefect_eq_absNorm_maxPowDividing`: this number is the absolute norm of the exact power of v dividing the principal ideal `(n)` of `𝓞 K`; no hypothesis on roots of unity is needed.
- `card_finitePlace_nthPowerQuotient_eq_defect`: the index formula written as `n · n · finitePlaceNthPowerDefect n v`.

## Proof

The index formula is the library's local formula `mixed_fieldIndex` for a mixed-characteristic local field, applied to `K_v` with its adic valuation; the kernel of the n-th power map has order n because the primitive root of K stays primitive in `K_v`. The second identity uses `d = e · f`, `N(v) = p^f` and `v(n) = e · v_p(n)`.

## Points to watch

- The index formula assumes that K contains a primitive n-th root of unity; it is not the general formula involving the roots of unity of `K_v`.
- The local-field structure on `K_v` (residue characteristic, the ℚ_p-structure that defines `d`) is the library's own construction from the adic valuation.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/GlobalClassFieldTheory/ClassFieldAxiom/IdeleClassPowerLocalUnitQuotient/FinitePlacePowerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `99e4a5e29487b5d0c8c63ac8600addd0a26143cd1b4271145fdf040485545295`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
