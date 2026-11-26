# Block triangularization by successive approximation

Module `Langlands.BushnellKutzko.SplitObstructionRiccati`. It holds the final argument of the
proof of Bushnell–Kutzko (1993), (2.3.12), printed pp. 63–64, in an abstract form over a
nonarchimedean local field `F`, followed by the reason, as in (2.3.5), printed p. 59, why the
resulting element does not generate a field.

## Idempotents

For complementary elements `ε₁ + ε₂ = 1` with `ε₁ ε₂ = 0` of a ring,
`mul_eq_zero_of_complement`, `idempotent_left_of_complement` and
`idempotent_right_of_complement` give `ε₂ ε₁ = 0`, `ε₁² = ε₁` and `ε₂² = ε₂`.

## The block commutator

`SplitObstruction.blockCommutator ε₁ ε₂ γ` is the `F`-linear map
`x ↦ (ε₁γε₁) x − x (ε₂γε₂)` on `A = End_F(V)` (`blockCommutator_apply`). On the block
`ε₁Aε₂` it is the map `d_γ(x) = γ₁₁ x − x γ₂₂` of (2.3.5).

## Main theorem

`SplitObstruction.not_isField_of_blockCommutator`. Let `𝓛` be an `𝔬_F`-lattice chain and
`ε₁, ε₂ ∈ 𝔓^0` complementary nonzero idempotents. Let `γ ∈ A` and `r ∈ ℤ`, and assume:

- `ε₂ γ ε₁ ∈ 𝔓^{−r}`;
- for every `j`, every element of `𝔓^{j−r} ∩ ε₁Aε₂` is the block commutator of an element of
  `𝔓^j ∩ ε₁Aε₂`;
- `ε₁ γ ε₂` is the block commutator of some element of `𝔓^1 ∩ ε₁Aε₂`, modulo
  `𝔓^{1−r} ∩ ε₁Aε₂`.

Then `¬ IsField (elementAlgebra γ)`.

## Proof

Write `W = ε₁Aε₂` (`offDiagonal`), `y = ε₁γε₂`, `z = ε₂γε₁` and `D` for the block
commutator.

1. `D` maps `W` into itself. The restriction is surjective by the second hypothesis and the
   exhaustion of the filtration. So it is bijective, as `W` is finite-dimensional. The
   inverse `e.symm` maps `𝔓^{j−r} ∩ W` into `𝔓^j`.
2. The map `Φ(t) = e.symm (y − t z t)` on `W` sends `𝔓^1 ∩ W` into itself, by the third
   hypothesis. If `t − t' ∈ 𝔓^m`, then `Φ t − Φ t' ∈ 𝔓^{m+1}`, because
   `t'zt' − tzt = −((t − t') z t' + t z (t − t'))`. The iterates of `Φ` from `0` therefore
   satisfy the hypotheses of `exists_limit` with `c = 1`. Their limit `L` lies in `W`, by
   separation, and is a fixed point of `Φ`. So `L ∈ 𝔓^1 ∩ W` solves the Riccati equation
   `D L + L z L = y`.
3. Since `L² = 0`, `1 + L` is invertible with inverse `1 − L`. For
   `γ' = (1 + L) γ (1 − L)`, the equation gives `ε₁ γ' ε₂ = 0`, `ε₁γ'ε₁ = ε₁γε₁ + L z` and
   `ε₂γ'ε₂ = ε₂γε₂ − z L`. Conjugation (`LinearEquiv.conjAlgEquiv`) maps `elementAlgebra γ`
   onto `elementAlgebra γ'`. So if `F[γ]` is a field, so is `F[γ']`.
4. The perturbed block commutator `x ↦ (ε₁γ'ε₁) x − x (ε₂γ'ε₂) = D x + L z x + x z L` is
   injective on `W`. If it kills `x ∈ 𝔓^k ∩ W`, then `D x ∈ 𝔓^{k+1−r}`, so `x ∈ 𝔓^{k+1}`.
   Hence `x` lies in every step and is zero.
5. If `K = F[γ']` is a field, then `V` is a `K`-vector space. Take `w₂ = ε₂ w₂ ≠ 0` and
   `w₁ = ε₁ w₁ ≠ 0`. A `K`-linear functional `f` with `f w₂ = 1`
   (`Module.Projective.exists_dual_eq_one`) gives the `K`-linear map `ψ = f(·) w₁`, and `ψ`
   commutes with `γ'`. Because `ε₁ γ' ε₂ = 0`, the element `x = ε₁ ψ ε₂ ∈ W` is killed by the
   perturbed block commutator. By step 4, `x = 0`, but `x w₂ = w₁ ≠ 0`.

The source constructs the conjugating element as a limit of successive unipotent
conjugations. Step 2 replaces this by a single contraction on the first filtration step of
the block. Step 5 replaces the eigenvalue argument of (2.3.5) by an `F[γ']`-linear map.
