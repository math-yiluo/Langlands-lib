# Termination of the smoothening sequence: generators of `J` via Krull's intersection theorem

Author: Worker 348. Internal helper module for Kaletha–Prasad, Theorem A.6.2. It uses Mathlib's
Krull intersection theorem (`Ideal.mem_iInf_smul_pow_eq_bot_iff`) and multivariate polynomials.

Namespace: `Langlands.GroupScheme.IntegralModel.Smoothening.Termination`.

Setting: an `R`-algebra `C` with point `ε`, augmentation ideal `I`, `ϖ ∈ R`,
`ptIdeal ε ϖ = ε⁻¹(ϖ R)` (written `𝔪`), elements `z k` and `x j` of `I`, and an ideal `J ⊇ ϖ C`
containing the `z k`.

- `GradedIndep ε ϖ x J`: every homogeneous polynomial `P` of degree `n` with `P(x) ∈ J + 𝔪^(n+1)`
  has all coefficients in `𝔪`.
- `exists_isHomogeneous_of_mem_span_pow` and `eval_mem_mul_span_pow`: elements of `(x)^n` are
  values of homogeneous polynomials of degree `n`.
- `exists_one_sub_mul_mem`: in a Noetherian ring, if `y ∈ 𝔞 + 𝔪^N` for all `N`, then
  `(1 - r) y ∈ 𝔞` for some `r ∈ 𝔪`.
- `augIdeal_le_of_le_mul`: `I ≤ (z) + (x) + 𝔪 I` implies `I ≤ (z) + (x) + 𝔪^N` for every `N`.
- `mem_step`, `le_span_sup_pow`, `sq_inf_le_sup_pow`: assume `GradedIndep`. Then a degree-by-degree
  argument gives `J ≤ (ϖ) + (z) + 𝔪^N` and `I² ∩ J ≤ ϖ I² + (z) I + 𝔪^N` for every `N`.
- `exists_mul_eq_of_mem_J` and `exists_mul_eq_of_mem_sq`: over a local ring `R` with `ϖ` in the
  maximal ideal and `C` Noetherian, the explicit forms needed by `exists_relation`. There is `g`
  with `ε g` a unit and `g J ⊆ ϖ C + ∑ z_k C`; this `g` is uniform because `J` is finitely
  generated. Each `q ∈ I² ∩ J` satisfies `h q ∈ ϖ I² + ∑ z_k I` with `ε h` a unit.
