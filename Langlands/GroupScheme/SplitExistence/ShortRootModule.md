# The short-root module and its raising and lowering operators (`ShortRootModule`)

Author: Worker 239.

Let `P : RootDatum J X Y` be reduced with finite `J`, let `b` be a base, and let
`gen : Fin r → X` be a family of weights. This module defines a free `ℤ`-module with a weight
basis and, for each simple root, an explicit raising and lowering operator on it. It proves
that the raising operator of one simple root commutes with the lowering operator of another.
The module is designed so that its weights generate `X`: `ChevalleyLieExistence` takes for
`gen` a family of generators of `X`.

## Matrices with one nonzero entry per column

- `colMat f κ` (for `f : B → B`, `κ : B → ℤ`) sends the basis vector `c` to `κ c · e_{f c}`.
  `colMat_apply` gives its entries.
- `colMat_mul`: `colMat f κ · colMat g μ = colMat (f ∘ g) (c ↦ κ (g c) · μ c)`.
- `colMat_congr`: two such matrices are equal if the coefficients agree and the targets agree
  wherever the coefficient is nonzero.
- `submatrix_eq_colMat`: recognizes a reindexed matrix as a `colMat`.
- `colMat_map_ne_zero`: a `colMat` with some coefficient `1` is nonzero modulo every prime.

## Facts about roots

These lemmas live in the `Roots` section.

- `root_reflectionPerm_eq`: `α_{s_i k} = α_k − ⟨α_k, α_i^∨⟩ α_i`.
- `eq_zero_of_smul_root_eq_zero`: `z α_i = 0` forces `z = 0`.
- `root_reflectionPerm_eq_self_iff`: `s_i` fixes `α_k` exactly when `⟨α_k, α_i^∨⟩ = 0`.
- `root_ne_neg_self`: `α_i ≠ −α_i`.
- `toLinearMap_reflection_coroot`: `⟨s_j x, α_i^∨⟩ = ⟨x, α_i^∨⟩ − ⟨x, α_j^∨⟩⟨α_j, α_i^∨⟩`.
- `IsShortRoot.neg_one_le_pairing`, `IsShortRoot.pairing_le_one`: one-sided versions of the
  shortness bound.
- `pairing_le_zero_of_mem_support` and `pairing_cases_of_mem_support` (finite `J`, reduced
  `P`): two distinct simple roots have nonpositive pairings. The pair of pairings is `(0, 0)`,
  `(−1, −1)`, `(−1, ≤ −2)` or `(≤ −2, −1)`, by Mathlib's `Base.pairingIn_le_zero_of_ne` and the
  table `pairing_pairing_mem`.

## The basis

- `ShortIdx P`: the subtype of short roots (`IsShortRoot`, from `ShortRoots`).
- `MinIdx P gen`: the subtype of weights `ν` that lie in `minimalWeights P (gen w)` for some
  `w` (the minimal-norm weights of the cosets `gen w + ℤΦ`, from `MinimalWeights`). It is
  finite.
- `Idx P b gen = (b.support ⊕ ShortIdx P) ⊕ MinIdx P gen`. Its basis vectors are written
  `u_t`, `v_γ` and `x_ν`.
- `idxWt`: the weights `0` for `u_t`, `α_γ` for `v_γ`, and `ν` for `x_ν`.
- `shRefl i γ`, `coe_shRefl`, `coe_shRefl_self`: the reflection `s_i` on short roots.
  `minIdx_reflection_mem`, `minRefl`, `coe_minRefl`: the reflection `s_i` on minimal-norm
  weights (`reflection_mem_minimalWeights`). `minIdx_pairing`: every `ν` in `MinIdx` pairs
  with every coroot to `−1`, `0` or `1`.

## The operators

For a simple root `i`, `raiseMat i = colMat (raiseTgt i) (raiseCoeff i)` and
`lowerMat i = colMat (lowerTgt i) (lowerCoeff i)`. The raising operator acts as follows:

- `u_t ↦ |⟨α_t, α_i^∨⟩| v_{α_i}` if `α_i` is short, and `u_t ↦ 0` otherwise;
- `v_{−α_i} ↦ u_i`;
- `v_γ ↦ v_{s_i γ} = v_{γ + α_i}` if `γ ≠ −α_i` and `⟨α_γ, α_i^∨⟩ = −1`, and `v_γ ↦ 0`
  otherwise;
- `x_ν ↦ x_{s_i ν} = x_{ν + α_i}` if `⟨ν, α_i^∨⟩ = −1`, and `x_ν ↦ 0` otherwise.

The lowering operator is the mirror image: `u_t ↦ |⟨α_t, α_i^∨⟩| v_{−α_i}` if `α_i` is short,
`v_{α_i} ↦ u_i`, and `v_γ ↦ v_{γ − α_i}`, `x_ν ↦ x_{ν − α_i}` when the pairing is `+1`. The
`Eval` section consists of the evaluation lemmas `raiseTgt_inl_inl`, `raiseCoeff_inl_inl`,
`raiseTgt_of_eq`, `raiseCoeff_of_ne`, `lowerTgt_inr` and similar, which compute these values
case by case.

## Commutation

- `comm_arith`: an integer identity for the generic case. Let `a = ⟨x, α_i^∨⟩ ≥ −1` and
  `c = ⟨x, α_j^∨⟩ ≤ 1`, and let `p = ⟨α_i, α_j^∨⟩ ≤ 0` and `q = ⟨α_j, α_i^∨⟩ ≤ 0` with
  `p = 0 ↔ q = 0`. Then "first lower along `j`, then raise along `i`" is possible exactly when
  "first raise along `i`, then lower along `j`" is. When it is possible, `a = −1`, `c = 1` and
  `p = q = 0`.
- `ite_one_zero_mul_ite_one_zero`: a product of two `0/1` indicators.
- `raiseMat_mul_lowerMat_comm` (reduced `P`): for distinct simple roots `i ≠ j`,
  `raiseMat i · lowerMat j = lowerMat j · raiseMat i`. Both sides are `colMat`s by
  `colMat_mul`, so it suffices to compare targets and coefficients column by column
  (`colMat_congr`). The columns are handled as follows.
  - On `u_t`, both composites vanish.
  - On `v_γ` with `γ = α_j` or `γ = −α_i`, the cases `(p, q)` of `pairing_cases_of_mem_support`
    are checked one by one. When `p = q = −1`, both composites send `v_{α_j}` to `v_{α_i}`, and
    `v_{−α_i}` to `v_{−α_j}`. Shortness of `γ` excludes `|q| ≥ 2` when `γ = α_j`, and `|p| ≥ 2`
    when `γ = −α_i`.
  - On the other `v_γ` and on all `x_ν`, apply `comm_arith` to the weight of the vector.

## Provenance

The module is a Lie-algebra analogue of the adjoint representation restricted to the short
roots, together with small "minuscule-type" summands. It is a construction internal to this
project, chosen so that every root string on the basis has length at most two and every
operator is explicit. For the classical adjoint and minuscule representations used in
Chevalley's construction, compare Steinberg, *Lectures on Chevalley groups*, §§1–2, and Geck,
*On the construction of semisimple Lie algebras and Chevalley groups* (Proc. AMS 145, 2017).
This module does not follow those constructions: in particular it does not prove that the
operators satisfy the Serre relations.
