# Algebra of a separable quadratic extension

Author: Worker 105.

This module supplies the field-theoretic input for the Galois-twisted line of Conrad's
Example 5.13 (Brian Conrad, *Weil and Grothendieck approaches to adelic points*, 2011,
printed p.20). It contains no statement from the paper. The content is standard: for a
separable quadratic extension `K'/K`, the ring `K' ⊗_K K'` is a product of two copies of `K'`.
Here this is expressed through ring maps out of `K'`.

## Declarations

- `QuadraticConj K K'` records:
  - a `K`-algebra automorphism `σ` of `K'` with `σ (σ x) = x`;
  - an element `θ` with `σ θ ≠ θ`;
  - the fact that every `α : K'` is `a + b θ` with `a b : K`.
- `QuadraticConj.nonempty` constructs such data when `finrank K K' = 2` and `K'/K` is
  separable. The extension is then Galois with automorphism group of order two
  (`IsGalois.card_aut_eq_finrank`). Take `σ` to be the non-identity automorphism and `θ` any
  element it moves. Then `1, θ` are linearly independent, hence a basis.
- `QuadraticConj.exists_eq_of_fixed`: elements fixed by `σ` lie in `K`.
- `splitIdem D μ₁ μ₂`. Let `μ₁ μ₂ : K' →+* Γ` be two ring maps into a commutative ring that
  agree on `K`. Then `splitIdem D μ₁ μ₂` is the element `(μ₂ θ − μ₁ (σ θ)) · μ₁ (θ − σ θ)⁻¹`.

## Properties of `splitIdem`

All of these assume that `μ₁` and `μ₂` agree on `K`.

- `splitIdem_quad`: `(μ₂ θ − μ₁ θ)(μ₂ θ − μ₁ σθ) = 0`, because the trace and the norm of `θ`
  lie in `K`.
- `splitIdem_isIdempotentElem`: `splitIdem` is idempotent.
- `splitIdem_mul` / `one_sub_splitIdem_mul`: `e (μ₂ α − μ₁ α) = 0` and
  `(1 − e)(μ₂ α − μ₁ (σ α)) = 0` for every `α`. These are first proved for `α = θ`
  (`splitIdem_mul_θ`, `one_sub_splitIdem_mul_θ`), then extended by writing `α = a + b θ`.
- `splitIdem_unique`: `splitIdem` is the only element with these two properties. The proof is a
  `linear_combination` computation from the four identities at `θ`, using that
  `μ₁ (θ − σθ)` is a unit (`splitIdem_unit`).
