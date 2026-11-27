# Components of sums of generalized joint eigenvectors

Module `Langlands.Global.CuspidalTestExpansion.GeneralizedEigenComponents`
(namespace `Langlands.Global.GeneralizedEigenComponents`). It contains pure linear algebra over
`ℂ`, used to show that the summands of an exponent decomposition are finite combinations of
translates of the sum.

## Declarations

- `aeval_apply_mem`: a submodule `W` invariant under an endomorphism `S` is invariant under
  `aeval S p` for every polynomial `p` (induction on `p` via `Polynomial.induction_on'`).
- `aeval_X_sub_C_pow`: `aeval S ((X - C α) ^ N) = (S - α • 1) ^ N`.
- `mem_of_sum_mem`: let `T : B → Module.End ℂ V` be a pairwise commuting family, `W` a
  submodule invariant under every `T b`, and `c : ι → V` such that each `c i` (`i ∈ s`) is a
  generalized joint eigenvector with character `χ i`: for every `i ∈ s` and every `b` there is
  an exponent `k` (which may depend on both `i` and `b`) with `((T b - χ i b • 1) ^ k) (c i) = 0`.
  Assume the characters `χ i` are pairwise distinct on `s`. If `∑ i ∈ s, c i ∈ W`, then every
  `c i ∈ W`.

## Proof of `mem_of_sum_mem`

Strong induction on the cardinality of `s`. If `s` has two indices `i₀ ≠ i₁`, pick `b` with
`χ i₀ b ≠ χ i₁ b` and put `α = χ i₀ b`. Split `s` into `s₀` (where `χ i b = α`) and `s₁` (the
rest), both proper subsets. With `N` the sum over `s` of the nilpotency exponents `k_i` of the
`c_i` for this `b`, `P = (T b - α • 1)^N`
kills every `c i`, `i ∈ s₀`, and preserves `W` and each generalized eigenspace; on the summands of
`s₁` it is invertible, by Bézout for the coprime polynomials `(X - α)^N` and `(X - χ i b)^{k_i}`
(`Polynomial.isCoprime_X_sub_C_of_isUnit_sub`). Hence `P (∑ c) = ∑_{s₁} P c_i ∈ W`; by induction
each `P c_i ∈ W`, and applying the Bézout inverse polynomial (which preserves `W` by
`aeval_apply_mem`) gives `c_i ∈ W` for `i ∈ s₁`. Then `∑_{s₀} c_i ∈ W`, and the induction
hypothesis applied to `s₀` finishes. A one-element `s` is immediate.
