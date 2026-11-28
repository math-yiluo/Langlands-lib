# Kloosterman sums over a finite field

Lean module: `Langlands.Representation.AffineGeneric.Kloosterman`, namespace
`Langlands.AffineGeneric`.

Let `k` be a finite field and `ψ : AddChar k ℂ`.

## Declarations

- `kloosterman ψ n A = Σ_{s ∈ kⁿ, s₁ ⋯ sₙ = A} ψ(s₁ + ⋯ + sₙ)`, the `n`-variable Kloosterman
  sum `Kl_n(ψ, A)`.
- `addChar_sum`: `ψ(Σᵢ fᵢ) = ∏ᵢ ψ(fᵢ)`.
- `sum_ite_ne_zero`: if `ψ ≠ 1`, then `Σ_{t ≠ 0} ψ(t) = -1`, since the full sum vanishes
  (`AddChar.sum_eq_zero_of_ne_one`).
- `sum_kloosterman`: if `ψ ≠ 1`, then `Σ_{A ≠ 0} Kl_n(ψ, A) = (-1)ⁿ`. Exchanging the sums, the
  left side is `Σ_{s ∈ (kˣ)ⁿ} ∏ᵢ ψ(sᵢ) = (Σ_{t ≠ 0} ψ(t))ⁿ`.
- `exists_kloosterman_ne_zero`: if `ψ ≠ 1`, some `A ≠ 0` has `Kl_n(ψ, A) ≠ 0`.
- `sum_prod_eq_one`: if every `cᵢ ≠ 0`, then
  `Σ_{r ∈ kⁿ, r₁ ⋯ rₙ = 1} ψ(Σᵢ rᵢ cᵢ) = Kl_n(ψ, c₁ ⋯ cₙ)`, by the change of variables
  `sᵢ = rᵢ cᵢ`, a bijection of `kⁿ` taking `∏ rᵢ = 1` to `∏ sᵢ = ∏ cᵢ`.
- `exists_addChar_ne_one`: `k` has a nontrivial complex additive character
  (`AddChar.exists_apply_ne_zero`).

These are standard elementary facts about Kloosterman sums; the proofs are direct.
