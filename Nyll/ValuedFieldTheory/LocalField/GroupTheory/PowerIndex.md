# Indices of `n`-th powers in commutative groups

Module `Nyll.ValuedFieldTheory.LocalField.GroupTheory.PowerIndex`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a commutative group `G` and `n : ℕ`, the file studies the quotient `G/Gⁿ` by the subgroup of `n`-th powers and the `n`-torsion subgroup `G[n]`, as the range and kernel of Mathlib's `powMonoidHom n`. It shows how both behave under isomorphisms, products, a splitting `G ≅ U × ℤ`, and passage to additive notation. These are the counting tools behind computations such as `[K^× : K^×ⁿ]` for a local field.

## Main results

- `card_nthPowerQuotient_eq_nthPowerKernel`: for finite `G`, `#(G/Gⁿ) = #G[n]`.
- `powMonoidHom_range_index_le`: the `H.index`-th powers of elements of `G` lie in `H`, for a subgroup `H`.
- Transport along `e : G ≃* H`: `nthPowerQuotientEquivOfMulEquiv`, `nthPowerKernelEquivOfMulEquiv`, and transfer of finiteness; `finite_nthPowerKernel_of_injective` pulls finiteness of `n`-torsion back along an injective homomorphism.
- `powMonoidHom_ker_units_eq_rootsOfUnity` and the instance `finite_powMonoidHom_ker_units`: for a commutative ring `R`, the `n`-torsion of `Rˣ` is `rootsOfUnity n R`, finite when `R` is a domain and `n ≠ 0`.
- Products: `nthPowerProductQuotientEquiv` and `nthPowerKernelProductEquiv` split `(G × H)/(G × H)ⁿ` and `(G × H)[n]` into factors, with `Nat.card` and `Cardinal` forms, and versions through `e : G ≃* H × U`.
- Integers: in `Multiplicative ℤ`, the `n`-th powers are `nℤ` (`powMonoidHom_range_multiplicativeInt_eq_integerMultipleSubgroup`); for `n ≠ 0` the quotient has `n` elements and the `n`-torsion is trivial.
- `card_nthPowerQuotient_eq_mul_of_mulEquiv_units_prod_int`: if `G ≃* U × ℤ` and `n ≠ 0`, then `#(G/Gⁿ) = n · #(U/Uⁿ)`; `card_nthPowerKernel_eq_of_mulEquiv_units_prod_int` gives `#G[n] = #U[n]`; `finite_nthPowerQuotient_of_mulEquiv_units_prod_int` gives finiteness from that of `U/Uⁿ`.
- Additive translation: for an additive commutative group `A`, `nsmulAddSubgroup A n` and `nsmulAddKernel A n` (image and kernel of `x ↦ n • x`) match the multiplicative range and kernel in `Multiplicative A`. Through a "logarithm" `e : G ≃* Multiplicative A`, `#(G/Gⁿ) = #(A/nA)`, `#G[n] = #A[n]`, and `Gⁿ` is the preimage of `nA` (`powMonoidHom_range_eq_comap_nsmulAddSubgroup_toSubgroup_of_mulEquiv`). `card_additive_nsmulQuotient_eq_nsmulKernel` is the finite additive version of the first result.

## Proofs

The finite equality is `Subgroup.index_range` (first isomorphism theorem). The product formula for quotients comes from the surjection `G × H → G/Gⁿ × H/Hⁿ`, whose kernel is computed to be `(G × H)ⁿ`; the one for `n`-torsion is checked coordinatewise.

## Watch for

- The `Nat.card` statements carry `Finite` hypotheses, on each quotient or kernel or (in the two finite kernel–quotient equalities) on the group itself; on an infinite type `Nat.card` is `0`. The `Cardinal` forms need none.
- The `Nat.card` and finiteness statements for `U × ℤ` require `n ≠ 0`; for `n = 0` the integer factor is infinite. The two `Cardinal` forms for `U × ℤ` hold for every `n`.
- `finite_nthPowerQuotient_of_mulEquiv_units_prod_int` is a theorem, not an instance: the splitting must be supplied.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/GroupTheory/PowerIndex.lean`: the Lean file is the source byte for byte (SHA-256 `3862b63f9473095de78a1be24ccfe8f5646e03f30612b58be3845f8d632ea880`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
