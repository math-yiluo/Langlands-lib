# Characteristic polynomials of path Coxeter products

This module is pure linear algebra over an arbitrary commutative ring `R`, in the namespace
`Langlands.LinearAlgebra.PathCoxeter`. It computes the characteristic polynomials of products of
"simple factors" on the lines of a path with `2 k + 3` vertices. It also covers the products in
which two neighbouring factors in the middle are replaced by an arbitrary `3 × 3` block with two
prescribed zero entries.

The module is an internal prerequisite of the split even-path cross-section task
(`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement`, Steinberg 1965, §9.15–9.19). There,
on a path representation, a simple root element times its canonical representative acts as a
simple factor. A pattern factor acts as a `3 × 3` block on three consecutive path lines. The group
theory is not part of this module.

**Provenance: internal.** The module has no counterpart in the literature. Steinberg's §9 proves
the cross-section by other means, and the formulas here were derived for this project.
Every result is stated in full below and proved in Lean.

## Conventions

Matrices are `Matrix (Fin n) (Fin n) R`, and lines are indexed by natural numbers.

- `vget v j`: coordinate `j : ℕ` of `v : Fin n → R`, and `0` if `j ≥ n`. It is injective
  (`vget_injective`) and additive, and `vget_fin`, `vget_of_lt`, `vget_of_le`, `vget_add`,
  `vget_smul` and `vget_single` compute it.
- Actions on families `f : ℕ → R`:
  - `sfacAct i c f` replaces `f i` by `-c f i + f (i+1)` and `f (i+1)` by `-f i`.
  - `coreAct j β f` replaces `f (j+r)`, for `r < 3`, by `β r 0 f j + β r 1 f (j+1) + β r 2 f (j+2)`.
  - `pprodAct a k c f` replaces `f a` by `Σ_{i<k} -c(a+i) f(a+i) + f(a+k)` and `f b`, for
    `a < b ≤ a + k`, by `-f (b-1)`.
  - `pathAct k c β = pprodAct 0 k c ∘ coreAct k β ∘ pprodAct (k+2) k c`.

## Definitions

- `sfac n i c` (**simple factor**): the matrix whose columns are `e_i ↦ -c e_i - e_(i+1)` and
  `e_(i+1) ↦ e_i`. It fixes every other basis vector.
- `pprod n a k c`: the ordered product `sfac n a (c a) * sfac n (a+1) (c (a+1)) * ⋯ *
  sfac n (a+k-1) (c (a+k-1))`, written as the list product over `List.range k`.
- `coreLin n j β` and `core n j β`: the linear map, and its matrix, that applies the `3 × 3` block
  `β : ℕ → ℕ → R` (entries `β r s` for `r, s < 3`) to the lines `j, j+1, j+2` and fixes the
  other lines. That is, `core n j β (j+r) (j+s) = β r s`, and `core` agrees with the identity
  outside the block.
- `pathMat k c β = pprod (2k+3) 0 k c * core (2k+3) k β * pprod (2k+3) (k+2) k c`. This is the
  path product on `2k+3` lines in which the two factors on the lines `k, k+1, k+2` are replaced
  by the block `β`.
- `pathVec k β : ℕ → R[X]`: the explicit vector used in the proof of `charpoly_pathMat`.
- `ordCore σ τ`: the block with rows `(-σ, -τ, 1)`, `(-1, 0, 0)` and `(0, -1, 0)`.
  `core_ordCore` shows that it is the block of `sfac j σ * sfac (j+1) τ`.

## Results

- **Action lemmas.** `vget_sfac_mulVec`, `vget_pprod_mulVec`, `vget_core_mulVec` and
  `vget_pathMat_mulVec` say that `vget (M *ᵥ v)` is the corresponding action applied to `vget v`,
  provided the lines lie in range. `sfac_mulVec_apply`, `core_apply` and `pathMat_apply` give the
  entries, and `pprodAct_zero`, `pprodAct_succ`, `pprodAct_self`, `pprodAct_of_lt`,
  `pprodAct_of_gt`, `pprodAct_of_mid`, `coreAct_of_lt`, `coreAct_of_ge`, `coreAct_add` and the
  `pathAct_*` lemmas evaluate the actions.
- **Base change.** `sfac_map`, `pprod_map`, `core_map` and `pathMat_map`: applying a ring
  homomorphism entrywise commutes with the constructions.
- `pprod_zero`, `pprod_succ` and `pprod_add`: splitting ordered products.
- **Cramer's rule.** `mul_det_eq_of_mulVec`: if `A *ᵥ x = p e_0` for a square matrix `A` of size
  `N + 1`, then `x 0 * det A = p * det A'`. Here `A'` deletes row and column `0`.
  `charpoly_eq_of_mulVec`: let `P` have size `N + 1` with rows and columns `1, …, N` lower
  triangular. Suppose `(X - P) x = p e_0` for a vector `x` over `R[X]` with
  `x 0 = ∏_{i<N} (X - P_(i+1,i+1))`. Then `charpoly P = p`.
- `pathMat_succ_succ_of_lt`, `pathMat_succ_succ_self` and `prod_X_sub_C_pathMat_diag`: if
  `β 1 2 = β 2 2 = 0`, then rows and columns `1, …, 2k+2` of `pathMat k c β` are lower
  triangular. The only nonzero diagonal entry among them is `β 1 1`, at line `k + 1`.
- **`charpoly_pathMat`** (general middle block). Assume `β 1 2 = 0` and `β 2 2 = 0`. Put
  `Y = X - β₁₁` and `W = β₂₀ Y + β₁₀ β₂₁`. Then the characteristic polynomial of `pathMat k c β` is

  `Y (X^(2k+2) + Σ_{i<k} (-1)^i c_i X^(2k+1-i) + (-1)^(k+1) β₀₀ X^(k+1))`
  `+ (-1)^(k+1) β₀₁ β₁₀ X^(k+1)`
  `+ β₀₂ W (Σ_{i<k} (-1)^(k+i) c_(k+2+i) X^(k-i) - 1)`.

  The coefficients `c_k` and `c_(k+1)` do not occur. Those two factors are replaced by `β`.
- **Commutation.** `commute_of_act`: two matrices commute if their actions on `vget` do.
  `sfac_commute_sfac` (`i + 2 ≤ j`), `sfac_commute_core` (`i + 2 ≤ j`) and `core_commute_sfac`
  (`j + 3 ≤ i`): factors on disjoint lines commute.
- **`charpoly_prod_perm`** (order independence). Let `y : ℕ → Matrix m m R` satisfy
  `Commute (y i) (y j)` whenever `i + 2 ≤ j`. Then for every list `l` that is a permutation of
  `List.range N`, `(l.map y).prod` and `((List.range N).map y).prod` have the same characteristic
  polynomial. `charpoly_prod_perm_mul` is the version with an extra right factor `Z`.
- **`charpoly_pprod`** (ordinary path product). The product of the `2k+2` simple factors on
  `2k+3` lines, in increasing order, has characteristic polynomial
  `X^(2k+3) + Σ_{j<2k+2} (-1)^j c_j X^(2k+2-j) - 1`.
- **`charpoly_pathMat_pattern`** (pattern block). Assume in addition `β 1 1 = 1`, `β 2 1 = 0` and
  `β 0 2 * β 2 0 = -1`. Then the characteristic polynomial of `pathMat k c β` is
  `(X - 1) Q + (-1)^(k+1) β₀₁ β₁₀ X^(k+1)`, where

  `Q = X^(2k+2) + Σ_{i<k} (-1)^i c_i X^(2k+1-i) + (-1)^(k+1) β₀₀ X^(k+1)`
  `+ Σ_{i<k} (-1)^(k+1+i) c_(k+2+i) X^(k-i) + 1`.

- `sum_range_two_mul_add_two`: splits a sum over `range (2k+2)` at `k` and `k+1`.

## Proof as implemented

**Actions.** All matrices are handled through their actions on `ℕ`-indexed families. Products
become compositions of actions (`vget_pprod_mulVec` is proved by induction on `k` using
`pprodAct_succ`). The block matrix `core` is defined as `LinearMap.toMatrix'` of the linear map
`coreLin`, so its action holds by definition. Entries follow by applying the action to a basis
vector.

**`charpoly_pathMat`.** Apply `charpoly_eq_of_mulVec` with `N = 2k+2` and `x = pathVec k β`:

- `x_i = (-1)^i X^(2k+1-i) Y` for `i ≤ k`;
- `x_(k+1) = (-1)^k β₁₀ X^(k+1)`;
- `x_i = (-1)^i X^(2k+2-i) W` for `k+2 ≤ i ≤ 2k+2`.

Its first entry `X^(2k+1) Y` is the product of the diagonal terms
(`prod_X_sub_C_pathMat_diag`). The identity `(X - P) x = p e_0` is checked row by row using
`pathMat_map` (the matrix over `R[X]`) and the `pathAct_*` lemmas. Rows `1, …, k` and
`k+3, …, 2k+2` only shift coordinates. Rows `k+1` and `k+2` use `β 1 2 = β 2 2 = 0`. Row `0`
gives the stated polynomial after splitting the two sums and collecting terms with `ring`.

`charpoly_eq_of_mulVec` combines Cramer's rule `mul_det_eq_of_mulVec` with the fact that
deleting row and column `0` of `X - P` leaves a lower triangular matrix. That minor has
determinant `x 0`, which is monic, so it can be cancelled.

**Commutation.** Factors on disjoint lines have commuting actions. This is checked pointwise by
case analysis (`split_ifs`, `omega`), and `vget_injective` transfers it to the matrices.

**`charpoly_prod_perm`.** By induction on `N`, with an auxiliary right factor `Z` that commutes
with every `y i` for `i + 2 ≤ N`. Write `l = l₁ ++ N :: l₂`. Every factor of `l₂` commutes with
`Z`, so `l₂` can be moved past `Z`. Then `charpoly (A B) = charpoly (B A)`
(`Matrix.charpoly_mul_comm`) rotates the product to `(l₂ ++ l₁) · (y N * Z)`, and the induction
hypothesis applies to the permutation `l₂ ++ l₁` of `range N` with right factor `y N * Z`.

**`charpoly_pprod`.** `core_ordCore` and `pprod_add` give
`pathMat k c (ordCore (c k) (c (k+1))) = pprod 0 (2k+2) c` (`pathMat_ordCore`). Then specialize
`charpoly_pathMat`, split the sum with `sum_range_two_mul_add_two`, and finish with `ring`.

**`charpoly_pathMat_pattern`.** Substitute the hypotheses into `charpoly_pathMat`. The result
follows by `linear_combination (X - 1) (S - 1) · (β₀₂ β₂₀ = -1)`, where `S` is the upper sum.
