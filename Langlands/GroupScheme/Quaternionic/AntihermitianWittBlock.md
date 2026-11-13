# Witt block decompositions of trace-valued antihermitian forms

Lean module: `Langlands.GroupScheme.Quaternionic.AntihermitianWittBlock`
(namespace `Langlands.GroupScheme.AntihermitianSplitRank`).

Setting: `σ` an involution of the first kind of a division algebra `D` over a field `K`,
`H ∈ M_n(D)` (`n` a finite linearly ordered type) invertible and trace-valued
`σ`-antihermitian (`σ.IsAntihermitian H`), of Witt index `r = σ.wittIndex H`. The form is the
Library's `h(x, y) = σ.sesqForm H x y = ∑ i j, x i * H i j * σ (y j)` on row vectors.

Main results:

* `wittGram HU`, for `HU ∈ M_d(D)`, is the block matrix
  `[[0, 1, 0], [-1, 0, 0], [0, 0, HU]]` on `(Fin r ⊕ Fin r) ⊕ Fin d`
  (`Matrix.fromBlocks (Matrix.fromBlocks 0 1 (-1) 0) 0 0 HU`).
* `exists_wittBlockBasis hH hu`: there are `d : ℕ`, a bijection
  `ε : n ≃ (Fin r ⊕ Fin r) ⊕ Fin d`, a matrix `P ∈ M_n(D)` and `HU ∈ M_d(D)` with `P` a unit,
  `HU` trace-valued `σ`-antihermitian, and
  `(P * H * σ.matrix n P) i j = wittGram HU (ε i) (ε j)` for all `i, j`.

This strengthens `exists_wittBasis` of `AntihermitianWittBasis`, which only records which
entries of `P H ᵗP^σ` vanish. The exact block form is what the general-degree Darboux
construction (`DegreeSplittingDarboux`) needs.

## Provenance

This is the classical Witt decomposition of a nondegenerate trace-valued antihermitian form
into `r` hyperbolic planes and an orthogonal complement (see Tits 1966, Table II, for its role
in the index of `SU(D, h)`). The statement is an internal auxiliary result, phrased for its use
in `DegreeSplittingDarboux`.

## Proof

The proof repeats the construction in the proof of `exists_wittBasis` and keeps track of the
Gram values.

* `exists_hyperbolic_family` (from `AntihermitianWittBasis`) gives `x, y : Fin r → n → D` with
  `h(x_k, x_l) = 0`, `h(y_k, y_l) = 0` and `h(x_k, y_l) = δ_{kl}`. `sesqForm_swap_ite` (same
  module) gives `h(y_k, x_l) = -δ_{kl}`.
* `U` is the kernel of the `D`-linear map `v ↦ (h(v, x_k), h(v, y_k))_k`. By rank–nullity,
  `|n| ≤ 2r + dim U`. Let `d = dim U` and `bU` a basis of `U`. Elements of `U` are orthogonal to
  all `x_k`, `y_k` on both sides (the other side by `IsAntihermitian.sesqForm_swap`).
* The family `p = (x, y, bU)` is linearly independent. Pairing a relation with `y_l` kills the
  `x_l`-coefficient, pairing with `x_l` kills the `y_l`-coefficient, and the remaining relation
  is one in the basis `bU`. Hence `|(Fin r ⊕ Fin r) ⊕ Fin d| = |n|`. Let `ε` be a bijection
  (`Fintype.equivOfCardEq`) and let `P` have rows `p (ε i)`.
* `P` is a unit. The map `v ↦ v ᵥ* P` is injective (independent rows), hence surjective
  (`LinearMap.injective_iff_surjective`). Solving for the standard basis vectors gives `Q` with
  `Q P = 1`, and `mul_eq_one_symm` gives `P Q = 1`.
* `HU` is the Gram matrix `(h(bU a, bU b))_{a b}`. It is antihermitian by
  `IsAntihermitian.sesqForm_swap`, and trace-valued by `sesqForm_self_mem_alternatingSubspace`.
* The entry identity: `(P H ᵗP^σ) i j = h(p (ε i), p (ε j))` (`mul_mul_matrix_apply`). A
  nine-case check on the summands of `ε i` and `ε j` matches it with `wittGram HU`.
