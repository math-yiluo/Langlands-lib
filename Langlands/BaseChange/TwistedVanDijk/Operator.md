# The kernel operators of the twisted van Dijk formula

Module `Langlands.BaseChange.TwistedVanDijk.Operator`. With the notation of
`Langlands.BaseChange.TwistedVanDijk.KernelFunction`, let `P i` be admissible representations
of the blocks `GL_{n_i}(E)` with σ-intertwiners `A i`, `τ = B.blockTensor P` their tensor
product representation of the Levi `M`, and `A₁ ⊗ ⋯ ⊗ A_r = leviTensorIntertwiner σ B A`. The
module turns the kernel values into test functions on `M` and assembles the operators
`(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(k(g, y))` into a linear map into the normalized product induction.

## Levels

A `Level σ φ` for `φ : G → ℂ` is an open subgroup `K'` of `G` contained in `K = GL_n(𝒪_E)`,
stable under the entrywise actions of `σ` and of `σ⁻¹`, under which `φ` is invariant on both
sides. Being open in the compact group `K`, it is compact open.

- `Level.inner` is `K'` as a subgroup of `K`, `Level.Cosets` the quotient `K/K'`, which is
  finite (`Level.cosetsFintype`: an open subgroup of a compact group has finite index), and
  `Level.rep x ∈ G` the chosen representative of a coset `x`.

## Kernel test functions and operators

- `kernelTest σ B μU L g y` is the kernel value `m ↦ δ_P(m)^{1/2} ∫_U φ(g⁻¹ σ(m u y)) du` as a
  test function on `M`: it is locally constant because `φ` is right invariant under the open
  subgroup `K'`, and of compact support because `φ` is (`isLocallyConstant_kernelValue`,
  `hasCompactSupport_kernelValue`).
- `kernelOperator σ B μU μM hP A L g y = (A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(kernelTest g y)`, where `τ(ψ)` is
  the integrated action `Hecke.integratedAction μM τ` of a test function.
- `kernelOperator_mul`: for `p ∈ P` with Levi part `m_p`,
  `kernelOperator (p g) y = δ_P(m_p)^{1/2} τ(m_p) ∘ kernelOperator g y`. Write `p = σ(q)` with
  `q ∈ P` (`parabolicAut`); the covariance `kernelValue_entrywiseAut_mul` makes
  `kernelTest (p g) y` equal to `δ_P(m_q)^{1/2}` times the left translate of `kernelTest g y`
  by `m_q`; the integrated action of a left translate is `τ(m_q) ∘ τ(·)`
  (`Hecke.integratedAction_leftTranslate`); the intertwining relation
  `(A₁ ⊗ ⋯ ⊗ A_r) ∘ τ(m_q) = τ(σ(m_q)) ∘ (A₁ ⊗ ⋯ ⊗ A_r)` and `σ(m_q) = m_p`,
  `δ_P(σ(m_q)) = δ_P(m_q)` (`leviModulus_leviAut`) conclude.
- `kernelTest_mul_right_left`, `kernelTest_mul_right_right`: the kernel test function is right
  invariant under `K'` in `g` and in `y` (`kernelValue_mul_right_left`,
  `kernelValue_mul_right_right`, using `σ(K') ⊆ K'`).

## The operator from functions on the cosets

Let `c = μK(K')` be the mass of the level for the Haar probability measure `μK` of `K`.

- `compactSum ... L f g = ∑_{x ∈ K/K'} c (A₁ ⊗ ⋯ ⊗ A_r) τ(k(g, rep x)) f(x)` for
  `f : K/K' → ⊗ W_i`.
- `compactSum_mul_left`: for `p ∈ P`, `compactSum f (p g)` is the twisted representation
  `δ_P^{1/2} · τ ∘ leviProjection` at `p` applied to `compactSum f g`, by `kernelOperator_mul`.
  This is the covariance defining the normalized product induction.
- `compactSum_mul_right`: `compactSum f` is right invariant under `K'`.
- `compactOperator ... L : (K/K' → ⊗ W_i) →ₗ[ℂ] Ind` sends `f` to the smooth induced function
  `compactSum f` (`Induction.smoothFunctionOf`, with the two previous items);
  `eval_compactOperator` evaluates it.
- `compactOperator_mem_fixedVectors`: its values are fixed by `K'` in the normalized product
  induction.
