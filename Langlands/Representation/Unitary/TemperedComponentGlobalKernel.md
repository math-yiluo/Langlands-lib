# The global kernel of the smoothed maps `j ∘ π(ψ_k)`

Module `Langlands.Representation.Unitary.TemperedComponentGlobalKernel` works with the data of
`Langlands.Analysis.TemperedIrreducibleComponentStatement`: a unitary jointly continuous `π` on
`H`, a closed `π`-invariant subspace `H₀` with orthogonal projection `P₀`, a jointly continuous
`π_W` on `W`, an equivariant bounded `j : H → W`, and a family of test functions `ψ_k` (`k : κ`).

## Definitions

| Declaration | Content |
| --- | --- |
| `wSub j H₀`, `coe_wSub` | `W₀`, the closure of `j(H₀)`, a closed submodule with carrier `closure (j '' H₀)` |
| `opT μ π hπ j ψ hψ k` | `T_k = j ∘ π(ψ_k)` |
| `opA μ π hπ j H₀ ψ hψ k` | `A_k = P₀ ∘ T_k^*` |
| `globalKernel` | `F⁰ (k, k', x, w, w') = ⟪A_k w, x (A_{k'} w')⟫` for `x ∈ algebra μ π hπ` |
| `globalRel ... nIdx` | the relations `(nIdx n, π(a) π(ψ_k), k, (π_W(ψ_{nIdx n}) π_W(a))^*)` for `n : ℕ`, words `a` and `k : κ`, and `(k, 1, k, P_{W₀})` |

## Results

* `starProjection_commute_of_unitary`: the projection onto a closed subspace invariant under a
  unitary representation commutes with it; with `intertwiner_comp_wordOp` and
  `intertwiner_comp_testOp` this gives `starProjection_wordOp` and `starProjection_testOp`, and the
  equivariance of `j` gives `j_wordOp`, `j_testOp`.
* `adjoint_opA`: `A_k^* = T_k ∘ P₀`.
* `globalKernel_star_mul`: `F⁰ (k, k', x^* y, w, w') = ⟪x (A_k w), y (A_{k'} w')⟫`, so `kernelOf F⁰`
  is a Gram kernel.
* `adjoint_word_opA`: `(π(a) π(ψ_k))^* A_{k₀} = A_k (π_W(ψ_{k₀}) π_W(a))^*`, the adjoint of
  `A_{k₀}^* π(a) π(ψ_k) = j π(ψ_{k₀}) P₀ π(a) π(ψ_k) = π_W(ψ_{k₀}) π_W(a) j π(ψ_k) P₀`.
* `opA_starProjection_wSub`: `A_k P_{W₀} = A_k`, because `T_k` maps `H₀` into `W₀`, so `T_k^*`
  maps `W₀^⊥` into `H₀^⊥`.
* `isConeElement_globalKernel`: `F⁰` is a cone element (`Langlands.Analysis.KernelCone.IsConeElement`)
  for `globalRel`; positivity and the domination `ρ(a)^* ρ(a) ≤ ‖a‖²` come from the Gram form and
  `‖a ξ‖ ≤ ‖a‖ ‖ξ‖`, the relations from the two previous items.
* `isBoundedForm_globalKernel`, `re_globalKernel_diag` (`Re F⁰ (k, k, 1, w, w) = ‖A_k w‖²`).

## Provenance

Internal. `F⁰` is built from the projected adjoints `A_k = P₀ T_k^*`, maps from `W` into `H` with
image in `H₀`; in the application the `T_k = j ∘ π(ψ_k)` are the maps assumed Hilbert–Schmidt. In the
direct-integral argument sketched in the Markdown of
`Langlands.Analysis.TemperedIrreducibleComponentStatement`, on a separable cyclic subspace `H₁ ⊆ H₀`
with `H₁ = ∫ H_z`, the corresponding projected adjoints restrict to `W₁ = closure (j(H₁))` and are
pointwise defined, with fibre maps `a_{ψ_k,z} : W₁ → H_z` (J. Bernstein, *On the support of
Plancherel measure*, 1988, §1.3, maps `S → H_z`, and §1.5); the maps `B_{ψ_k,z} : H_z → W₁` are
their Hilbert adjoints (§1.4). The kernel `F⁰` packages all the `A_k` at once, without
decomposing `H₀`.
