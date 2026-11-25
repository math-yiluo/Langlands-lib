# The relative idele norm as a product of Galois conjugates

Module `Nyll.ClassFieldTheory.AlgebraicNumberTheory.Idele.Extension.GaloisNorm`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

For a finite Galois extension `L/K`, the file proves that the determinant norm on `A ⊗_K L` over an arbitrary nontrivial commutative `K`-algebra `A`, pushed back into `A ⊗_K L`, is the product of the `Gal(L/K)`-conjugates. With `A = 𝔸_K` and the model `𝔸_L = 𝔸_K ⊗_K L`, this gives `inclusion K L (norm K L a) = ∏_σ σ(a)` for every relative idele `a`.

## Main declarations

- `normPolynomial b`: for a basis `b` of `L/K`, the multivariate polynomial over `K`, built from the constant coefficient of `polyCharpoly` of multiplication, whose value at the coordinates of `x` is `Algebra.norm K x` (`eval_normPolynomial`).
- `conjugatePolynomial b σ` and `galoisProductPolynomial b`: linear polynomials over `L` giving `σ x` at the coordinates of `x`, and their product over `σ`.
- `map_normPolynomial_eq_galoisProductPolynomial` (`L/K` Galois, `K` infinite): `normPolynomial b`, with coefficients in `L`, equals the product polynomial. Both sides agree on points with coordinates in `K` by Mathlib's `Algebra.norm_eq_prod_automorphisms`, and such points suffice since `K` is infinite.
- `baseChangedLmul_eq`, `eval₂_normPolynomial_baseChange`: base change of the regular representation, and the fact that evaluating `normPolynomial b` at the coordinates of `z ∈ A ⊗_K L` gives `Algebra.norm A z`, through `LinearMap.polyCharpoly_baseChange`.
- `scalarConjugation A σ`: the map `id ⊗ σ` on `A ⊗_K L`; `eval₂_conjugatePolynomial_baseChange` evaluates the conjugate polynomials on it.
- `includeLeft_norm_eq_prod_scalarConjugations` (`L/K` Galois, `K` infinite, `A` nontrivial): `N_A(z) ⊗ 1 = ∏_σ (id ⊗ σ)(z)`.
- `adeleInclusion_norm_eq_prod_conjugates` and `inclusion_norm_eq_prod_conjugates` (`K` a number field, `L/K` Galois): the formula for relative adeles and for relative ideles, `inclusion K L (norm K L a) = ∏ σ • a`.

## Points to watch

- The general formula assumes `K` infinite. The relative idele norm is the library's determinant norm on its model `𝔸_K ⊗_K L`, not Mathlib's ideles of `L`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AlgebraicNumberTheory/Idele/Extension/GaloisNorm.lean`: the Lean file is the source byte for byte (SHA-256 `1fb48a950fad1ca95ec598cd9dc35d6631677d7de13850ecb658c3f18fcbdd6e`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.
