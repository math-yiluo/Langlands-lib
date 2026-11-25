# The norm quotient Kˣ/N(Lˣ)

Module `Nyll.ValuedFieldTheory.LocalField.NonarchimedeanLocalField.NormQuotient`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a field extension `L/K`, this file defines the norm subgroup `N(Lˣ) ≤ Kˣ` and the quotient group `Kˣ/N(Lˣ)`, the group that local class field theory compares with the Galois group of an abelian extension. It supplies the quotient map, the universal property and comparison isomorphisms, so that later files need not unfold the quotient.

## Definitions

- `localNormSubgroup K L`: the range of the norm `normUnits K L : Lˣ →* Kˣ`.
- `NormQuotient K L`: `Kˣ ⧸ localNormSubgroup K L`, as a separate definition with a commutative group instance; `normQuotientConcreteEquiv` identifies it with the concrete quotient.
- `normClass K L : Kˣ →* NormQuotient K L`, the quotient map, and `NormQuotient.inductionOn`: every class is `normClass K L x` for some `x`.
- `normQuotientLift f h`: the homomorphism induced by `f : Kˣ →* M` that kills all norms; `normQuotientLift_surjective`: it is surjective when `f` is.
- `normQuotientEquivOfSurjective`: the first isomorphism theorem, `NormQuotient K L ≃* M` for a surjective `f` whose kernel is exactly the norm subgroup.
- `normQuotientEquivOfSubgroupEq`, `normQuotientEquivOfNormSubgroupEq`, `normQuotientMapOfLE`: the isomorphisms and maps induced by an equality or an inclusion of subgroups, the last two comparing two extensions `L` and `M` of `K`.

## Results

- `normClass_ker`, `normClass_eq_one_iff`, `normClass_eq_one_iff_mem`: a class is trivial exactly when its representative is a norm.
- `normClass_eq_iff_div_mem`, `normClass_eq_iff_exists_norm_div`, `normClass_eq_iff_exists_norm_mul_left` and `_right`: two classes agree exactly when the representatives differ by a norm.
- Multiplying a representative by a norm, or by an integer power of a norm, does not change its class.
- `localNormSubgroup_self` and the instance `normQuotient_self_subsingleton`: for `L = K` every unit is a norm and the quotient is trivial.
- `normClass_eq_all_of_normUnits_surjective`, `normClass_eq_of_localNormSubgroup_eq_top`: if every unit is a norm, all classes coincide.

The proofs are direct applications of Mathlib's `QuotientGroup` API.

## Points to watch

- Nothing here is specific to local fields, and no finiteness is assumed on `L/K`. For an infinite extension Mathlib's `Algebra.norm` is constantly `1`, so the norm subgroup is trivial and the quotient is all of `Kˣ`.
- The module comment announces a relation between the cardinality of the quotient and the index of the norm subgroup; no such statement is in this file.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/LocalField/NonarchimedeanLocalField/NormQuotient.lean`: the Lean file is the source byte for byte (SHA-256 `d1a8bbe6e43b8aa7b4dbf3229ff2e98039cbec8574ce11bcbc352c73d98c3ed1`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
