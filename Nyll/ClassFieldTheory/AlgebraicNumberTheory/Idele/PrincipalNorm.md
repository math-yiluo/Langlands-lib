# The product formula for principal ideles

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.PrincipalNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a number field K, this file proves the product formula in idelic form: the absolute idele norm is 1 on the diagonal copy of Kˣ. As a result the norm descends to the idele class group C_K = I_K / Kˣ, and the file defines the norm-one idele classes.

## Main definitions and results

- `InfiniteIdeleGroup.archimedeanNorm_principalIdele`: for x ∈ Kˣ, the archimedean norm of the principal idele of x is |N(x)|, the absolute value of the field norm of x from K to ℚ. The proof uses Mathlib's product formula `NumberField.prod_abs_eq_one` together with `FinitePlace.prod_eq_inv_abs_norm`.
- `FractionalIdealGroup.absoluteNorm`: the absolute norm of a nonzero fractional ideal, as a unit of ℝ≥0.
- `FractionalIdealGroup.absoluteNorm_prime`, `absoluteNorm_factorization` and `absoluteNorm_toPrincipalIdeal`: on the prime p_v this norm is N(p_v); it agrees with the norm of the exponent vector; and the principal ideal (x) has norm |N(x)|.
- `FiniteIdeleGroup.absoluteNorm_eq_fractionalIdealAbsoluteNorm`: the finite part of the idele norm is the absolute norm of the fractional ideal attached to the finite idele.
- `FiniteIdeleGroup.absoluteNorm_principalIdele`: on a principal idele the finite part is |N(x)|.
- `IdeleGroup.finite_absoluteNorm_eq_archimedeanNorm_principalIdele` and `IdeleGroup.absoluteNorm_principalIdele`: the two factors agree on principal ideles, so principal ideles have absolute norm 1. `principalSubgroup_le_normOneSubgroup` is the same fact stated for subgroups.
- `IdeleClassGroup.absoluteNorm`: the norm on C_K, with `absoluteNorm_mk` computing it on a representative.
- `IdeleClassGroup.normOneSubgroup`: the kernel of the norm on C_K. `comap_normOneSubgroup` and `mk_mem_normOneSubgroup_iff` say that its preimage in the ideles is exactly the norm-one subgroup.

## Points to watch

- `FractionalIdealGroup K` and the absolute norms are the library's own definitions, with values in ℝ≥0ˣ. The idele norm (from `Idele.NormCore`) is the finite part divided by the archimedean part. It is the reciprocal of the usual ∏_v |a_v|_v, which does not change the kernel or the product formula.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/PrincipalNorm.lean`: the Lean file is the source byte for byte (SHA-256 `86b39c03bfcc6a4d35cc341d6a5860f8a2563d8ef0a8e4ec138f45ecada2fdf9`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
