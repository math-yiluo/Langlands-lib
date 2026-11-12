# Rational lattices of finite adelic matrices

Author: Worker 19.

Let `𝔸_f` be the finite adeles of `ℚ` (`FiniteAdeles ℚ`), `Ẑ ⊆ 𝔸_f` the
integral finite adeles (`integralFiniteAdeles ℚ`), and `ϕ : ℚ → 𝔸_f` the
diagonal embedding. This module proves two decompositions:

- `exists_rat_mul_integral`: every invertible square matrix `X` over `𝔸_f`
  factors as `X = B W` with `B` an invertible rational matrix and `W` an
  integral matrix whose inverse `X⁻¹ B` is also integral. In group form,
  `GL_n(𝔸_f) = GL_n(ℚ) · GL_n(Ẑ)`.
- `exists_pos_rat_mul_unit`: every unit `c` of `𝔸_f` is `r u` with `r` a
  positive rational and `u` a unit of `Ẑ`. In group form,
  `𝔸_f^× = ℚ_{>0} · Ẑ^×`.

Both are steps of the finiteness proof for `GJ(ℚ)\GJ(𝔸_f)/K` for definite
unitary groups, which Harris (1999), §3–4, uses. In that proof a finite
adelic similitude acts on a lattice `Ẑ^n`, and the rational matrix `B`
gives a `ℤ`-basis of the corresponding rational lattice.

## Provenance

The decomposition `GL_n(𝔸_f) = GL_n(ℚ) GL_n(Ẑ)` is the classical fact that
`ℚ` has class number one, in lattice form. The proof here is the standard
lattice argument, written for this module from published Library results:

- strong approximation for `ℚ`: `exists_sub_mem_integralFiniteAdeles`
  (`𝔸_f = ℚ + Ẑ`);
- bounded denominators of finite adeles: `exists_mul_mem_integralFiniteAdeles`;
- `ℚ ∩ Ẑ = ℤ`: `exists_intCast_eq_of_mem_integralFiniteAdeles`.

The last two live in the module `Langlands.Shimura.Unitary.PositiveArithmeticFinite`
(published).

## Declarations

### Integral matrices

- `IsIntegral M` (definition): all entries of the `𝔸_f`-matrix `M` lie in
  `Ẑ`. Lemmas: `IsIntegral.mul`, `IsIntegral.intCast_smul`,
  `isIntegral_map_intCast` (integer matrices are integral) and
  `isIntegral_one`.
- `exists_int_of_isIntegral`: a rational matrix that is integral over `𝔸_f`
  is an integer matrix (`ℚ ∩ Ẑ = ℤ`, entrywise).
- `exists_intCast_mul_mem` and `exists_intCast_smul_isIntegral`: every
  finite adele, and every finite adelic matrix, has a nonzero integer
  multiple that is integral. For a matrix, take the product of the integers
  for its entries.
- `exists_rat_add_mul`: for a nonzero integer `N`, every `a ∈ 𝔸_f` is
  `ϕ(q) + N t` with `q ∈ ℚ` and `t ∈ Ẑ`. Apply strong approximation to
  `a / N`.

### The lattice of a matrix

- `InSpan B v` (definition): the vector `v ∈ 𝔸_f^ι` lies in `B Ẑ^ι`, that is
  `v = B w` with `w` integral. It is closed under addition, under
  multiplication by elements of `Ẑ`, and under finite sums (`InSpan.add`,
  `InSpan.smul`, `inSpan_zero`, `InSpan.sum`).
- `lattice X` (definition): for a square matrix `X` over `𝔸_f`, the
  `ℤ`-submodule of rational vectors `q` with `X⁻¹ q` integral
  (`mem_lattice`). Here `X⁻¹` is Mathlib's totalized inverse, which is `0`
  for singular `X`; for such `X` this set is all of `ℚ^ι` and is not
  `ℚ^ι ∩ X Ẑ^ι`.
- `mem_lattice_iff`: if `det X` is a unit, then `lattice X = ℚ^ι ∩ X Ẑ^ι`,
  that is `q ∈ lattice X` if and only if `q = X w` for some integral `w`.
  Take `w = X⁻¹ q`, and conversely `X⁻¹ (X w) = w`.
- `intCast_smul_single_mem`: if `N X⁻¹` is integral, then `N e_i` lies in
  `lattice X`.
- `exists_intCast_eq_mul_of_mem`: if `X` is invertible and `N X` is
  integral, then `N q` has integer entries for every `q ∈ lattice X`.
  Indeed `N q = (N X)(X⁻¹ q)` is integral and rational.

### `GL_n(𝔸_f) = GL_n(ℚ) GL_n(Ẑ)`

`exists_rat_mul_integral X hX`: for `X` with `det X` a unit there are a
rational `B` with `det B ≠ 0` and an `𝔸_f`-matrix `W` such that `W` is
integral, `X⁻¹ B` is integral, and `X = B W`.

Proof:

1. Choose a nonzero integer `N` with `N X` and `N X⁻¹` integral, and let
   `L = lattice X`. Then `N ℤ^ι ⊆ L ⊆ N⁻¹ ℤ^ι`.
2. `L` lies in the span of the `ℤ`-linearly independent vectors `N⁻¹ e_i`,
   so it is free with a finite basis (Mathlib's
   `Submodule.basisOfPidOfLESpan`).
3. Its rank is `|ι|`. The basis vectors are `ℤ`-independent, hence
   `ℚ`-independent (`LinearIndependent.iff_fractionRing`), so the rank is at
   most `|ι|`. The vectors `N e_i ∈ L` are independent, so it is at least
   `|ι|`.
4. Let `B` be the matrix whose columns are the basis vectors, indexed by
   `ι` through a bijection. Its columns are `ℚ`-independent, so `B` is
   invertible (`Matrix.linearIndependent_cols_iff_isUnit`). Every `q ∈ L`
   equals `B z` with `z` an integer vector.
5. The columns of `B` lie in `L`, so `X⁻¹ B` is integral.
6. Each column `x` of `X` lies in `B Ẑ^ι`. By `exists_rat_add_mul`,
   `x = ϕ(q) + N t` with `q` rational and `t` integral. Then
   `X⁻¹ ϕ(q) = e_j - (N X⁻¹) t` is integral, so `q ∈ L` and
   `ϕ(q) ∈ B Ẑ^ι`. Also `N t = Σ_i t_i N e_i` with `N e_i ∈ L`.
   Collecting the coefficient vectors of the columns gives `W` with
   `X = B W`.

### Finite ideles of `ℚ`

`exists_pos_rat_mul_unit c hc`: for a unit `c` of `𝔸_f` there are a
rational `r > 0` and `u, u' ∈ Ẑ` with `u u' = 1` and `c = ϕ(r) u`.

Proof: apply `exists_rat_mul_integral` to the `1 × 1` matrix `(c)`. This
gives `c = b w` with `b ∈ ℚ^×` and `w ∈ Ẑ`. The inverse `w⁻¹ = c⁻¹ b` is
integral because `X⁻¹ B` is. Replace `(b, w)` by `(-b, -w)` if `b < 0`.

## Qualifications

- Only the field `ℚ` is treated; for a number field of class number
  greater than one the decomposition fails, and nothing here addresses
  that case.
- Uniqueness of the decomposition (up to `GL_n(ℤ)`) and compactness of
  `GL_n(Ẑ)` are not part of this module.
