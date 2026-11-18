# The form dual to a weighted Gram matrix of a pairing

Module `Langlands.LinearAlgebra.GramDualForm`, namespace
`Langlands.LinearAlgebra.GramDual`.

This module builds the rational bilinear form used in the Casimir proof of
Freudenthal's multiplicity formula. In Humphreys (*Introduction to Lie Algebras
and Representation Theory*, GTM 9, §22) the form on weights is the one dual to
the restriction of the Killing form, or of the trace form of a faithful
representation, to the Cartan subalgebra. Here that restriction is written as
an explicit Gram matrix in coordinates, so that the form is defined over `ℚ`
on the character lattice. The construction is internal to this project; its
properties below are elementary linear algebra.

## Data

- `X`, `Y`: additive groups (characters and cocharacters);
- `P : X →ₗ[ℤ] Y →ₗ[ℤ] ℤ`: a pairing;
- `yb : Basis ι ℤ Y` with `ι` finite;
- `m : X → ℕ`: multiplicities, assumed finitely supported where needed
  (`hm : (support m).Finite`).

## Definitions

- `coord P yb : X →ₗ[ℤ] ι → ℚ`, `coord P yb χ j = ⟨χ, y_j⟩` (`coord_apply`).
- `gram P yb m : Matrix ι ι ℚ`, the Gram matrix
  `M = ∑ᶠ ν, m(ν) • c(ν) c(ν)ᵀ` with `c = coord P yb`. In the application `m(ν)`
  is the dimension of the weight-`ν` space, and `M_{jl}` is the trace of the
  product of the endomorphisms by which `y_j` and `y_l` act.
- `form P yb m : X →ₗ[ℤ] X →ₗ[ℤ] ℚ`,
  `form P yb m χ χ' = c(χ) ⬝ᵥ (M⁻¹ *ᵥ c(χ'))` (`form_apply`). Here `M⁻¹` is
  Mathlib's `Matrix.inv` (the inverse when `det M ≠ 0`).

## Results

- `support_subset_of_eq_zero`: a function vanishing wherever `m` does has
  support in `hm.toFinset`.
- `gram_eq_sum`, `gram_apply`: `M` as a finite sum over `hm.toFinset`, and
  entrywise `M_{jl} = ∑ᶠ ν, m(ν) (c(ν)_j c(ν)_l)`.
- `gram_transpose`: `Mᵀ = M`.
- `dotProduct_gram_mulVec`: `zᵀ M z = ∑_{ν ∈ hm.toFinset} m(ν) (c(ν) ⬝ᵥ z)²`.
- `eq_zero_of_dotProduct_gram_mulVec_eq_zero`: assume `hY`: every nonzero
  `y : Y` pairs nontrivially with some `ν` having `m ν ≠ 0`. Then `zᵀ M z = 0`
  implies `z = 0`.
- `det_gram_ne_zero`, `isUnit_det_gram`: under `hm` and `hY`, `det M ≠ 0`.
- `form_comm` (under `hm`): `F(χ, χ') = F(χ', χ)`.
- `form_pos` (under `hm`, `hY`, and `hX`: every nonzero `χ` pairs nontrivially
  with some `y`): `0 < F(χ, χ)` for `χ ≠ 0`.
- `form_apply_apply_eq` (under `hm`, `hY`): let `s : X ≃ X` and
  `s' : Y →ₗ[ℤ] Y` satisfy `⟨s χ, y⟩ = ⟨χ, s' y⟩` and `m (s ν) = m ν`. Then
  `F(s χ, s χ') = F(χ, χ')`. In the application `s` is a reflection of the root
  datum and `s'` the corresponding coreflection.

## Proofs

- `dotProduct_gram_mulVec`: expand `M` as a finite sum; each term contributes
  `m(ν) (z ⬝ᵥ c(ν)) (c(ν) ⬝ᵥ z)`.
- `eq_zero_of_dotProduct_gram_mulVec_eq_zero`: all terms of the sum of squares
  are nonnegative, so `c(ν) ⬝ᵥ z = 0` whenever `m ν ≠ 0`. Clearing denominators
  (`IsLocalization.exist_integer_multiples_of_finite`) gives a nonzero integer
  `b` and integers `z'_j` with `b z_j = z'_j`. The cocharacter
  `y = ∑_j z'_j y_j` satisfies `⟨ν, y⟩ = b (c(ν) ⬝ᵥ z) = 0` for all `ν` with
  `m ν ≠ 0`, so `y = 0` by `hY`; linear independence of the basis gives
  `z'_j = 0`, hence `z = 0`.
- `det_gram_ne_zero`: a nonzero kernel vector `z` of `M`
  (`Matrix.exists_mulVec_eq_zero_iff`) would have `zᵀ M z = 0`.
- `form_comm`: `M⁻¹` is symmetric because `M` is (`transpose_nonsing_inv`).
- `form_pos`: with `z = M⁻¹ c(χ)` one has `M z = c(χ)` and `F(χ, χ) = zᵀ M z ≥ 0`.
  If it were zero then `z = 0`, so `c(χ) = 0`, i.e. `⟨χ, y_j⟩ = 0` for all `j`,
  hence `⟨χ, ·⟩ = 0`, contradicting `hX`.
- `form_apply_apply_eq`: let `A` be the integer matrix with
  `A_{jl}` the `l`-th coordinate of `s'(y_j)`. Then `c(s χ) = A c(χ)`.
  Reindexing the finite sum defining `M` by `s` gives `M = A M Aᵀ`; hence
  `det A ≠ 0`, `M⁻¹ = (Aᵀ)⁻¹ M⁻¹ A⁻¹` and `Aᵀ M⁻¹ A = M⁻¹`. Therefore
  `F(s χ, s χ') = c(χ)ᵀ Aᵀ M⁻¹ A c(χ') = F(χ, χ')`.
