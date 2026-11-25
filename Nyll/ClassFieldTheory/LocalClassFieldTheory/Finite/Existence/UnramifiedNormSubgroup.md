# Units whose valuation is divisible by n

Module `Nyll.ClassFieldTheory.LocalClassFieldTheory.Finite.Existence.UnramifiedNormSubgroup`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a nonarchimedean local field `K` and a natural number `n`, this file defines the subgroup of `Kˣ` of elements whose normalized valuation is divisible by `n`, and identifies the quotient with `ℤ/nℤ` through the valuation reduced modulo `n`. This is the subgroup that the norm subgroup of the unramified extension of degree `n` is compared with.

## Main definitions and results

Write `v` for the normalized valuation `valuationMap K : Additive Kˣ →+ ℤ`.

- `valuationModDegree K n`: `v` reduced modulo `n`, as a map to `ZMod n`. It is surjective (`valuationModDegree_surjective`, from surjectivity of `v`), vanishes exactly when `n ∣ v(x)`, and takes equal values exactly when `n` divides the difference. `valuationModDegreeMulHom` is the multiplicative form, with the same lemmas.
- `unramifiedNormSubgroup K n`: the subgroup `{x ∈ Kˣ | n ∣ v(x)}`. `mem_unramifiedNormSubgroup_iff` holds by definition; `unramifiedNormSubgroup_eq_ker_valuationModDegreeMulHom` identifies it with the kernel of the reduced valuation.
- `unramifiedNormClass K n`: the quotient map `Kˣ → Kˣ / unramifiedNormSubgroup K n`, with surjectivity, kernel and triviality criteria; `unramifiedNormClass_eq_iff`: two units have the same class exactly when `n ∣ v(x) − v(y)`.
- `unramifiedNormQuotientEquivZMod K n`: an isomorphism of the quotient with `Multiplicative (ZMod n)`, sending the class of `x` to `v(x) mod n` (`unramifiedNormQuotientEquivZMod_mk`), obtained from the first isomorphism theorem. `unramifiedNormQuotientEquivZMod_eq_iff_valuation_sub_eq_zero` restates equality of images.
- `unramifiedNormQuotient_cardinal_eq_zmod`: for every `n`, the quotient has the cardinality of `ZMod n`.
- `finiteUnramifiedNormQuotient` (an instance) and `unramifiedNormQuotient_card_eq_degree`: for `n ≠ 0`, the quotient is finite of order `n`.

## Points to watch

- Despite its name, `unramifiedNormSubgroup` is defined by the valuation condition alone. That it is the norm subgroup of an unramified extension is not proved in this file.
- `n = 0` is allowed. Then the subgroup consists of the elements of valuation `0`, and the quotient is identified with `ZMod 0 = ℤ`, which is infinite. The finiteness and order statements require `[NeZero n]`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/Existence/UnramifiedNormSubgroup.lean`: the Lean file is the source byte for byte (SHA-256 `0b5a6d5acab7b2b41f8a038c5e711f23b8c08627496ada6f84655a77306c2bb7`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
