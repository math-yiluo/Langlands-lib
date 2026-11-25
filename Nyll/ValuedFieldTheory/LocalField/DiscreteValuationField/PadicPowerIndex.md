# The ℤ_p factor in the power-index formula for local fields

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PadicPowerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

The file computes `ℤ_p / nℤ_p` and its products, and feeds the result into the power-index formula for a local field `K`: `(K^× : K^×n) = n · #μ_n(K) / |n|`, where `|n|` is the normalized absolute value. It covers mixed characteristic, where the principal units are a finite group times `ℤ_p^d`, and equal characteristic, where they are a product of copies of ℤ_p and `n` is prime to `p`.

## Quotients of ℤ_p

- `padicIntNsmulQuotientEquivZMod`: for `n ≠ 0`, `ℤ_p / nℤ_p ≅ ZMod (p^(v_p(n)))`. `padicIntPiNsmulQuotientEquiv` does the same coordinatewise for an arbitrary product `ι → ℤ_p`.
- `card_padicInt_finPi_nsmulQuotient`: for `n ≠ 0`, the quotient of `ℤ_p^d` by `n` has `p^(d·v_p(n))` elements. `card_padicInt_pi_nsmulQuotient_of_coprime`: if `n` is prime to `p`, the quotient of any product of copies is trivial. `nsmulAddKernel_padicInt_pi_eq_bot`: multiplication by `n ≠ 0` is injective on such products.
- `card_finite_prod_padicInt_finPi_nsmulQuotient_eq_kernel_mul`: for finite `T` and `n ≠ 0`, the cokernel of `n` on `T × ℤ_p^d` has order `#ker(n) · p^(d·v_p(n))`.
- `normalizedLocalNatAbs p d n`: the rational number `p^(−d·v_p(n))`, standing for `|n|`.

## Index formulas

For `F` a complete discretely valued field (`CompleteDVF`) on `K` with finite residue field and a uniformizer, with `U` the units of the valuation ring and `U^1` the first principal units, and `n ≠ 0`:

- `card_fieldUnits_nthPowerQuotient_of_mixedPrincipalUnitStructure`: `(K^× : K^×n) = n · #μ_n(K) · p^(d·v_p(n))`. Its `_rationalFormula` form divides by `normalizedLocalNatAbs p d n`.
- `card_units_nthPowerQuotient_of_mixedPrincipalUnitStructure` and its `_fieldKernel` and `_rationalFormula` forms: `(U : U^n) = #μ_n(K) · p^(d·v_p(n))`, the first form with the `n`-torsion of `U` in place of `μ_n(K)`.
- `..._of_equalPrincipalUnitStructure` and `..._of_equalPrincipalUnitProduct`, field and unit versions with rational forms: if `n` is prime to `p`, `(K^× : K^×n) = n · #μ_n(K)` and `(U : U^n) = #μ_n(K)` (in one version, the `n`-torsion of `U`).

The proofs feed the ℤ_p computations into general index formulas from the imported power-index file.

## Watch for

- The structure theorem for principal units is a hypothesis: each formula takes an isomorphism `e` from `U^1` to `T × ℤ_p^d`, `T × (ι → ℤ_p)` or `ι → ℤ_p`, written multiplicatively, with `T` finite. Finiteness of `K^× / K^×n` (for the field versions) and of `U^1 / (U^1)^n` are also hypotheses.
- `p` and `d` are not tied to `F` in the statements; `p^(−d·v_p(n))` is the absolute value `|n|` in mixed characteristic when `p` is the residue characteristic and `d = [K : ℚ_p]`, and the equal-characteristic forms take `d = 0`.
- `normalizedLocalNatAbs p d 0 = 1`, not the absolute value of 0.
- `F` has its value group in universe 0, and `ι` lives in the universe of `K`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PadicPowerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `f4409cc8baf1a7261735c2a9a8eb6359f629313e30e16e6fb49d043a21058f2a`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
