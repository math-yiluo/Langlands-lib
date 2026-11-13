# Witt bases of trace-valued antihermitian forms

Lean module: `Langlands.GroupScheme.Quaternionic.AntihermitianWittBasis`
(namespace `Langlands.GroupScheme.AntihermitianSplitRank`).

Setting: `σ` an involution of the first kind of a division algebra `D` over a field `K`,
`H ∈ M_n(D)` (`n` a finite linearly ordered type) invertible and trace-valued
`σ`-antihermitian (`σ.IsAntihermitian H`), with the Library form
`h(x, y) = ∑ i j, x i * H i j * σ (y j)` on row vectors.

Main results:

* `exists_hyperbolic_family hH hu`: there are `x, y : Fin (σ.wittIndex H) → n → D` with
  `h(x_k, x_l) = 0`, `h(y_k, y_l) = 0` and `h(x_k, y_l) = if k = l then 1 else 0`.
* `exists_wittBasis hH hu`: there are an invertible `P` and weights
  `w : n → Fin (σ.wittIndex H) → ℤ` with
  `(P * H * σ.matrix n P) i j ≠ 0 → w i + w j = 0`, `∑ i, w i = 0`, and
  `∀ k, ∃ i, w i = Pi.single k 1`.

## Provenance

This is the classical Witt decomposition of a nondegenerate trace-valued antihermitian form
into hyperbolic planes and an orthogonal complement, which underlies the description of the
index of `SU(D, h)` in Tits 1966, Table II. The statements here are internal auxiliary results for
`AntihermitianSplitRankLower`, phrased for that use.

## Proof

Helpers: `sesqForm_sum_left/right`, `sesqForm_sub_left/right` (additivity), and
`exists_sesqForm_eq_apply`: for invertible `H`, every left `D`-linear form `f` on `D^n` is
`v ↦ h(v, z)` with `z = σ ∘ (H⁻¹ *ᵥ c)`, `c i = f (Pi.single i 1)`.

**Hyperbolic family.** Let `W = σ.wittSubspace H` (totally isotropic of dimension `r`, Library
`FormLemmas`) with basis `x`. Extend each coordinate form of `W` to `D^n`
(`LinearMap.exists_extend`) and represent it as `h(·, z_l)`: then `h(x_k, z_l) = δ_{kl}`.
The Gram matrix `g = (h(z_l, z_{l'}))` is trace-valued antihermitian (`sesqForm_swap`,
`sesqForm_self_mem_alternatingSubspace`), so `g = A - ᵗA^σ` (`exists_eq_sub_matrix`). Put
`y_l = z_l - ∑_k A l k • x_k`. Then `h(x_k, y_l) = δ_{kl}` and
`h(y_l, y_{l'}) = g l l' + σ (A l' l) - A l l' = 0`. In characteristic `2` the
trace-valued hypothesis is exactly what makes the diagonal of `g` alternating.

**Witt basis.** `U` is the kernel of `v ↦ (h(v, x_k), h(v, y_k))_k`, so by rank–nullity
`card n ≤ 2r + dim U`. The family `p = (x, y, basis of U)` is linearly independent: pairing a
relation with `y_l` and `x_l` kills the `x`- and `y`-coefficients, and the rest is a relation
in the basis of `U`. Hence `2r + dim U = card n`. Take `e : n ≃ (Fin r ⊕ Fin r) ⊕ Fin (dim U)`
and let `P` have rows `p (e i)`. `P` is invertible: `v ↦ v ᵥ* P` is injective (independent
rows), hence surjective, which gives `Q` with `Q * P = 1`, and matrices over a division ring
are Dedekind-finite (`mul_eq_one_symm`). The weights are `e_k` on `x_k`, `-e_k` on `y_k` and
`0` on `U`. The entries `(P H ᵗP^σ) i j = h(p (e i), p (e j))` (`mul_mul_matrix_apply`) vanish
unless the weights cancel: a nine-case check using `h(x, x) = h(y, y) = 0`,
`h(x_k, y_l) = δ_{kl}`, `h(y_k, x_l) = -δ_{kl}`, and orthogonality of `U` to `x, y` on both
sides (by `sesqForm_swap`). The weights sum to zero and `w (e⁻¹ (inl (inl k))) = e_k`.
