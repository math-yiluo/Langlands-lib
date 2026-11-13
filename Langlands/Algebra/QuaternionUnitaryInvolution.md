# The canonical involution of a quaternion division algebra and unitary involutions

Helper module for the proof of `Langlands.LocalUnitaryDivisionCommutativeStatement`.

`D` is a finite-dimensional central division algebra over a field `L`; `nrd L x` abbreviates the
Library reduced norm `reducedNorm L D L (1 ⊗ₜ x)`, and `reducedTrace L D` is the Library reduced
trace (`Langlands.Algebra.QuaternionCommutator`).

## Reduced norm

`nrd_mul`, `nrd_one`, `nrd_zero`, `nrd_ne_zero` (from `nrd x · nrd x⁻¹ = 1`) and
`nrd_algebraMap` (`nrd (algebraMap c) = c ^ reducedDegree`, via `reducedNorm_scalar`).

## Reduced degree two (`hd : reducedDegree L D = 2`)

`gamma L x = algebraMap (Trd x) - x` is the canonical involution.

* `cayleyHamilton`: `x² - Trd(x) x + Nrd(x) = 0` (Library `sq_sub_reducedTrace_add_reducedNorm`).
* `mul_gamma`, `gamma_mul_self`: `x · γ x = γ x · x = Nrd x`.
* `reducedTrace_algebraMap` (`Trd c = 2c`), `gamma_zero`, `gamma_algebraMap` (`γ c = c`),
  `gamma_add`, `gamma_gamma` (`γ (γ x) = x`, since `Trd (γ x) = Trd x`).
* `gamma_eq_nrd_mul_inv`: `γ x = Nrd(x) x⁻¹` for `x ≠ 0`; hence `gamma_mul`:
  `γ (x y) = γ y · γ x`, using multiplicativity of `nrd`; and `nrd_gamma`: `Nrd (γ x) = Nrd x`.

## With a unitary involution `τ` relative to `σ`

* `tau_cayleyHamilton`: applying `τ` gives `τx² - σ(Trd x) τx + σ(Nrd x) = 0`.
* `reducedTrace_tau_and_nrd_tau`: `Trd (τ x) = σ (Trd x)` and `Nrd (τ x) = σ (Nrd x)`.
  Subtracting the Cayley–Hamilton relation of `τ x` gives
  `(Trd(τx) - σ Trd x) · τx = Nrd(τx) - σ Nrd x` (scalars). If the scalar coefficient were
  nonzero, `τ x` and hence `x` would be scalars, for which both identities are direct.
* `gamma_tau`: `γ ∘ τ = τ ∘ γ`.
* `beta L τ = τ ∘ γ`; `beta_add`, `beta_mul` (`β` is multiplicative, as a composite of two
  anti-automorphisms), `beta_algebraMap` (`β c = σ c`), `beta_beta` (`β² = id`), `nrd_beta`
  (`Nrd (β x) = σ (Nrd x)`), `reducedTrace_beta`, and `betaHom` (`β` as a ring endomorphism).
