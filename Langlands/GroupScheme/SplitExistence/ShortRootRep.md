# The `SL₂`-representations of the simple roots on the short-root module (`ShortRootRep`)

Author: Worker 239.

Let `P : RootDatum J X Y` have finite `J`, let `b` be a base, and let `gen : Fin r → X`. For
every simple root `α_i`, this module builds an integral representation of `SL₂`
(`SL2Rep`, from `BlockRep`) on the short-root module `ℤ^(Idx P b gen)` of `ShortRootModule`.
The representation is attached to `α_i` and to the coroot functional `⟨·, α_i^∨⟩`, and its
raising and lowering operators are exactly `raiseMat i` and `lowerMat i`.

## Column-monomial matrices

These lemmas extend the `colMat` toolkit of `ShortRootModule`.

- `colMat_congr_inst`: `colMat_congr` across two `DecidableEq` instances.
- `colMat_zero`: `colMat f 0 = 0`.
- `submatrix_colMat`: reindexing a `colMat` along an equivalence `σ` gives
  `colMat (σ.symm ∘ f ∘ σ) (κ ∘ σ)`.
- `fromBlocks_colMat`: a block-diagonal sum of two `colMat`s is a `colMat`.
- `submatrix_map_ne_zero`: reindexing preserves being nonzero after a ring map.
- `cartE_one_eq_colMat`, `cartF_one_eq_colMat`: the Cartan-block operators of `WeylModule`
  as `colMat`s.

## Strings of length at most one

Fix `α : X` and `pair : X →+ ℤ` with `pair α = 2`.

- `eq_add_iff_of_abs_le`, `add_eq_iff_of_abs_le`: for weights `x`, `y` with pairings in
  `[−1, 1]`, `y = x + α` exactly when `pair x = −1` and `y = x − pair x • α`. Similarly
  `y + α = x` exactly when `pair x = 1` and `y = x − pair x • α`.
- `StringDecomp.ofRefl`: the decomposition `StringData.ofUnit` of `ShortRoots`, for an injective
  family with pairings in `[−1, 1]` and an explicit reflection map `f : C → C` on the index type.
  `ofRefl_E_one` and `ofRefl_F_one` show that its operators are `colMat f` with coefficient
  `1` exactly where the pairing is `−1`, respectively `+1`.

## Pieces of the module along a simple root

- `corootHom P i : X →+ ℤ` is `x ↦ ⟨x, α_i^∨⟩`. The lemmas `corootHom_apply`, `corootHom_root`
  and `corootHom_root_self` compute it.
- `root_reflectionPerm_eq_root_iff`, `root_reflectionPerm_eq_neg_root_iff`: `s_i α_k = ±α_i`
  exactly when `α_k = ∓α_i`.
- `ShortIdxNe P i`: the short roots other than `±α_i`. `shRefl_ne` and `shReflNe` give the
  reflection `s_i` on it.
- `shortNeDecomp i`: the short roots other than `±α_i` form strings of length at most one along
  `α_i`.
- `shortDecomp i`: if `α_i` is not short, all short roots do.
- `minDecomp gen i`: the minimal-norm weights do.

  All three are instances of `StringDecomp.ofRefl`, because short roots `γ ≠ ±α_i` and
  minimal-norm weights pair with `α_i^∨` into `[−1, 1]`. The lemmas `shortNeDecomp_E_one`,
  `shortNeDecomp_F_one`, `shortDecomp_E_one`, `shortDecomp_F_one`, `minDecomp_E_one` and
  `minDecomp_F_one` give their operators as `colMat`s.
- `cartSplit b gen i hi` (for short `α_i`): the equivalence
  `Idx P b gen ≃ (Fin 2 ⊕ b.support) ⊕ (ShortIdxNe P i ⊕ MinIdx P gen)`, which sends `v_{−α_i}`
  to `0 : Fin 2`, `v_{α_i}` to `1 : Fin 2`, the `u_t` to `b.support`, and the remaining vectors
  to the last summand. It is built from `cartSplitFun` and `cartSplitInv`, with the evaluation
  lemmas `cartSplitFun_of_eq`, `cartSplitFun_of_eq_neg`, `cartSplitFun_of_ne`,
  `cartSplitInv_zero`, `cartSplitInv_one`, `root_shRefl_self`, `cartSplit_apply` and
  `cartSplit_symm_apply`.

## The representations

- `shortCartanRep b gen i hi` (for short `α_i`): `SL2Rep.ofCartan` with the Cartan block on
  `v_{−α_i}`, `v_{α_i}` and the `u_t`, with coefficients `c_t = |⟨α_t, α_i^∨⟩|` (so
  `c_i = 2`). It is glued along `cartSplit` to the sum `shortNeDecomp i ⊕ minDecomp gen i`.
- `nonShortRep b gen i hi` (for `α_i` not short): `StringDecomp.toSL2Rep` of the sum of the
  trivial decomposition on the `u_t` (strings of length zero), `shortDecomp i` and
  `minDecomp gen i`.
- `shortCartanRep_E_one`, `shortCartanRep_F_one`, `nonShortRep_E_one`, `nonShortRep_F_one`:
  their operators `E 1`, `F 1` are `raiseMat i` and `lowerMat i`. Each side is written as a
  `colMat` (`cartE_one_eq_colMat`, `fromBlocks_colMat`, `submatrix_colMat`, the `_E_one` lemmas
  above). They are then compared with `colMat_congr` case by case on the basis vector.
- `simpleRep b gen i`: `shortCartanRep` or `nonShortRep`, according to whether `α_i` is short.
  `simpleRep_E_one` and `simpleRep_F_one` show that its operators are `raiseMat i` and
  `lowerMat i`.

## Nonvanishing

- `exists_raiseCoeff_eq_one`, `exists_lowerCoeff_eq_one` (reduced `P`): some coefficient of
  `raiseMat i` (respectively `lowerMat i`) equals `1`. If `α_i` is short, take the vector
  `v_{−α_i}`, which is sent to `u_i`. Otherwise `exists_isShortRoot_pairing_eq_neg_one` gives a
  short root `β` with `⟨β, α_i^∨⟩ = −1`, and `v_β` is sent to `v_{β+α_i}`. Combined with
  `colMat_map_ne_zero`, this shows that both operators are nonzero modulo every prime. That
  step happens in `ChevalleyLieExistence`.

## Provenance

The construction is internal to this project. It realizes, for each simple root, the
restriction to the root `SL₂` of the representation described in `ShortRootModule`. The
`SL₂`-representations involved are the standard integral ones of highest weight at most two
(Steinberg, *Lectures on Chevalley groups*, §2).
