# Reducing the power-index formula to principal units

Module `Nyll.ValuedFieldTheory.LocalField.DiscreteValuationField.PowerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `F` be a complete discretely valued field in the library's sense (`CompleteDVF`) on `K`, with finite residue field `k`, unit group `U` of the valuation ring and first principal units `U^1`. The file reduces the index `(K^× : K^×n)` to data on `U^1`. It uses the decompositions `K^× ≅ U × ℤ`, given by a uniformizer, and `U ≅ R × U^1`, where `R` is the Teichmüller root factor, isomorphic to `k^×`. Throughout, `μ_n(K)` is the kernel of `x ↦ x^n` on `K^×`, `U[n]` the `n`-torsion of `U`, and every equality is between cardinalities.

## Unconditional reductions

- Instances: `R` is finite; for `n ≠ 0` the `n`-torsion of `U` and of `U^1` is finite; `U / U^n` is finite when `U^1 / (U^1)^n` is. `finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits` (a theorem, not an instance) gives finiteness of `K^× / K^×n` from that of `U^1 / (U^1)^n`.
- `card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient`: `(K^× : K^×n) = n · (U : U^n)`.
- `card_unit_nthPowerQuotient_eq_mul_roots_principalUnit_nthPowerQuotient` and `card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel`: index and `n`-torsion of `U` split over `R × U^1`. `card_residueRoots_nthPowerQuotient_eq_nthPowerKernel`: on the finite factor `R`, index and kernel have the same size.
- `card_fieldUnits_nthPowerKernel_eq_unit_nthPowerKernel`: for `n ≠ 0`, `#μ_n(K)` equals the size of the `n`-torsion of `U`.

## Conditional formulas

- `card_unit_nthPowerQuotient_eq_mul_unitKernel_of_principalUnit_index` and `card_fieldUnits_nthPowerQuotient_eq_mul_fieldKernel_of_principalUnit_index`: if `(U^1 : (U^1)^n)` equals the size of the `n`-torsion of `U^1` times `c`, then `(U : U^n) = #U[n] · c` and `(K^× : K^×n) = n · #μ_n(K) · c`. Variants take `c = #k^a`.
- `..._of_logEquiv`: an isomorphism `e : U^1 ≃* Multiplicative A` transports index and torsion of `U^1` to cokernel and kernel of multiplication by `n` on `A`, so an additive computation `hadd` feeds the formulas above.
- `card_principalUnit_nthPowerQuotient_eq_residue_pow_of_image_eq`: if `(U^1)^n = U^m` with `m ≥ 1`, then `(U^1 : (U^1)^n) = #k^(m−1)`.
- `PowerIndex.unitQuotient_residuePow_of_principalImage`, `PowerIndex.fieldQuotient_residuePow_of_principalImage`: if `U^1` has no `n`-torsion and `(U^1)^n = U^(a+1)`, then `(U : U^n) = #U[n] · #k^a` and `(K^× : K^×n) = n · #μ_n(K) · #k^a`.

## Watch for

- The analytic input on `U^1` is always a hypothesis: the index identity `hprincipal`, the isomorphism `e` with the additive count `hadd`, or the image identity `hpow` with trivial torsion `hkernel`. The file does not prove any of them, so it gives the power-index formula only conditionally.
- Finiteness of `U^1 / (U^1)^n` is an instance hypothesis in most statements; the field-index formulas assume `K^× / K^×n` finite, `card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient` together with `U / U^n`.
- `n ≠ 0` (an instance `NeZero n`) is also assumed in `finite_fieldUnits_nthPowerQuotient_of_finite_principalUnits`, `card_fieldUnits_nthPowerQuotient_eq_mul_unit_nthPowerQuotient`, `card_unit_nthPowerKernel_eq_mul_roots_principalUnit_nthPowerKernel` and all conditional formulas for `U` and `K^×`.
- The field-level results also need a uniformizer `π`, through `hπ`; so do `card_principalUnit_nthPowerQuotient_eq_residue_pow_of_image_eq` and `PowerIndex.unitQuotient_residuePow_of_principalImage`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/DiscreteValuationField/PowerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `eb45c6c5613ec2c6f1927bbac1d44a9a360d28adfb6299c420ed1ff9f83ad192`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
