# Multiplication by n on ℤ̂ and the finite-index subgroups of ℤ̂

Module `Nyll.GaloisCohomology.ProfiniteIntegers.ProfiniteInteger`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file proves basic facts about the profinite integers `ℤ̂` (the library's `ZHat`) used to normalize a surjection onto `ℤ̂` in abstract valuation theory: multiplication by a positive integer `n` is an isomorphism of `ℤ̂` onto the closed subgroup `nℤ̂`, which is the kernel of reduction modulo `n` and has index `n`, and every subgroup of finite index has this form.

## Main results

- `zHatMulNat n`: multiplication by `n` as a continuous additive endomorphism of `ℤ̂`.
- `proCIntegerOne_pow_nat_injective`: distinct natural multiples of `1` in `ℤ̂` are distinct.
- `zHatMulNat_injective`: for `n > 0`, multiplication by `n` is injective.
- `isClosed_zHatMulNat_range`: `nℤ̂` is closed (it is compact).
- `zHatReduction_surjective`: reduction `ℤ̂ → ℤ/nℤ` is onto.
- `zHatMulNat_range_eq_ker_reduction`: for `n > 0`, `nℤ̂` is the kernel of reduction modulo `n`.
- `zHatMulNat_range_index`: `nℤ̂` has index `n`.
- `zHatAddSubgroup_eq_mulNat_range_of_index_ne_zero`, with variants for a prescribed index and for a finite quotient: every additive subgroup `H` of finite nonzero index equals `(index H)·ℤ̂`.
- `zHatMulNatRangeEquiv`, `zHatDivide`: for `n > 0`, `ℤ̂ ≃ₜ+ nℤ̂`, and the continuous inverse "division by `n`".

## Proofs

Injectivity reduces modulo `nm` for all `m` and cancels `n` in `ℤ/nmℤ → ℤ/mℤ`. For the kernel, an element of the kernel lies in the closure of the integers divisible by `n`, because the kernel is open and `ℤ` is dense in `ℤ̂`; `nℤ̂` is closed. The classification uses that `H` contains `(index H)·ℤ̂` (the index kills the quotient) and compares indices; closedness of `H` is not assumed. The homeomorphism comes from a continuous bijection from a compact space onto a Hausdorff space.

## Points to watch

- Finite-index subgroups need not be closed in the hypothesis; the conclusion shows they are.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/GaloisCohomology/ProfiniteIntegers/ProfiniteInteger.lean`: the Lean file is the source byte for byte (SHA-256 `c527ecc219d00b64c33ecb4e198dab910cbc106f5a5329a947e45f972ffd24d3`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
