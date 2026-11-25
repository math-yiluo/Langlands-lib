# Herbrand cohomology of the relative idele class group

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Cohomology.Herbrand`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K` of number fields with group `G = L ≃ₐ[K] L`, the file sets up the low-degree Tate cohomology of the exact sequence `1 → Lˣ → I_L → C_L → 1`. Here `I_L` is the library's relative idele group (units of `𝔸_K ⊗[K] L`), `G` acts by the conjugation coming from the tensor-product model, and `C_L` is the quotient by principal ideles.

## Main definitions and results

- `relativeIdeleMulDistribMulAction`, `ideleClassMulDistribMulAction`, `principalIdeleMulDistribMulAction`: the actions of `G` by group automorphisms on `I_L`, on `C_L`, and on the subgroup of principal ideles.
- `ideleClassNorm : C_L → C_K`, descended from the determinant norm, and `IdeleClassNormQuotient K L`, the quotient of `C_K` by its image.
- `relativeIdele_tateNorm_eq_inclusion_norm`, `classInclusion_ideleClassNorm_eq_tateNorm`: the Tate norm `∏_σ σ • a` equals the image of the determinant norm, on ideles and on idele classes (Galois product formula).
- `baseIdeleClassEquivFixed`: Galois descent `C_K ≃* C_L^G`; under it the norm image is the Tate-norm subgroup (`ideleClassNorm_range_map_equivFixed`), and the kernel of the Tate norm is the kernel of `ideleClassNorm` (`ideleClass_normKernelSubgroup_eq_ker`).
- `ideleClassHerbrandH0EquivNormQuotient`: the degree-zero group `HerbrandH0 G C_L` is isomorphic to `IdeleClassNormQuotient K L`; `ideleClassNorm_index_eq_herbrandH0_card` equates the index of the norm subgroup with `Nat.card` of that group. `ideleClassHerbrandHMinusOneEquiv` presents the degree −1 group as norm-one classes modulo the augmentation subgroup.
- `principalIdele_ideleClass_shortExact`: the inclusion of principal ideles and the quotient map form an equivariant short exact sequence.
- `relativeIdele_herbrandQuotient_eq_principal_mul_class`: if `σ` generates `G` and the degree 0 and −1 groups of principal ideles, of `I_L` and of `C_L` are all finite, then `h(I_L) = h(principal ideles) · h(C_L)`.
- `ideleClassHerbrandQuotientDefined_of_principal_relative`: finiteness for principal ideles and for `I_L` alone already makes the Herbrand quotient of `C_L` defined, with the same identity.

## Proofs

The product formula and Galois descent (injectivity of `C_K → C_L`, image the fixed classes) are imported; the multiplicativity results apply the general Herbrand-quotient theorems for short exact sequences.

## Points to watch

- The multiplicativity theorems assume that `G` is cyclic (hypothesis `hgen`) and take the finiteness of the cohomology groups as instance hypotheses; they are not proved here.
- The left term is the subgroup of principal relative ideles, the image of `Lˣ`, with the restricted action.
- With Mathlib's conventions, the index identity reads `0 = 0` when the norm quotient is infinite.
- `HerbrandH0` and `HerbrandHMinusOne` are the library's degree 0 and −1 groups for a finite group, the latter relative to a chosen element `σ`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Cohomology/Herbrand.lean`: the Lean file is the source byte for byte (SHA-256 `cdf9d8de1007d7159ca9f005abbaf952069046f13a0fff1f6679b2f1c1940c58`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
