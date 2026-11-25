# Coefficient bound for irreducible polynomials from uniqueness of extensions

Module `Nyll.ValuedFieldTheory.Valuation.AbsoluteValue.AlgebraicExtension.UniqueExtensionCoefficients`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

Let `v` be a nonarchimedean absolute value on `K` and `f` an irreducible polynomial over `K`. Suppose `v` has a unique nonarchimedean extension `w` to a splitting field `L` of `f`. The file shows that the largest coefficient value of `f` is the larger of `v(f₀)` and `v(lead f)`.

## Definitions and main results

- `IsUniqueNonarchimedeanAbsoluteValueExtension v w`: `w` is nonarchimedean and restricts exactly to `v`, and every nonarchimedean absolute value on `L` restricting to `v` equals `w`.
- `uniqueNonarchimedeanAbsoluteValueExtension_map_algEquiv_eq`: such a `w` satisfies `w(σ x) = w(x)` for every `K`-automorphism `σ` of `L`.
- `uniqueNonarchimedeanAbsoluteValueExtension_eq_on_roots_of_irreducible`: if `L/K` is normal, all roots in `L` of an irreducible polynomial over `K` have the same `w`-value.
- `abs_coeff_prod_X_sub_C_le_pow_card`: let `w` satisfy the strong triangle inequality, let `B ≥ 1`, and let every element of a multiset `s` have value at most `B`. Then every coefficient of the product of the `X − α`, `α ∈ s`, has value at most `B^|s|`.
- `abs_multiset_prod_eq_pow_card_of_eq`: if all elements of `s` have value `t`, their product has value `t^|s|`.
- `uniqueExtensionCoefficients_coeff_abs_le_endpoint_max_of_unique_extension`: for `L` a splitting field of the irreducible `f` and `w` as above, `v(fᵢ) ≤ max(v(f₀), v(lead f))` for all `i`.
- `uniqueExtensionCoefficients_polynomialCoeffAbsMax_eq_endpoint_max`: the same as an equality for `polynomialCoeffAbsMax v f`, the maximum of the coefficient values.

## Proof

Composing `w` with a `K`-automorphism gives another nonarchimedean extension, so uniqueness makes `w` invariant. Since the splitting field is normal, all roots are conjugate and share one value `t`. Write `f = lead(f) · ∏(X − α)`. If `t ≤ 1`, every coefficient is bounded by `v(lead f)`. If `t ≥ 1`, it is bounded by `v(lead f) · t^(deg f) = v(f₀)`.

## Points to watch

- Uniqueness of the extension to the splitting field is a hypothesis (`IsUniqueNonarchimedeanAbsoluteValueExtension`) and is not proved here. In the library it stands for the unique-extension theorem for henselian or complete fields.
- Uniqueness is required only among nonarchimedean extensions. "Nonarchimedean" is the library's `NonarchimedeanAbsoluteValue`, which the proofs use as boundedness on the image of `ℕ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ValuedFieldTheory/Valuation/AbsoluteValue/AlgebraicExtension/UniqueExtensionCoefficients.lean`: the Lean file is the source byte for byte (SHA-256 `b3f527576502beffb069394b71e045416fe57c21db108a3f9048e264914b4db8`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
