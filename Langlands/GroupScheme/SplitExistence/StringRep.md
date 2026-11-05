# Representations of `SL₂` assembled from root strings (`StringRep`)

Author: Worker 239.

Fix `α : X` and an additive map `pair : X →+ ℤ`, which stands for `⟨·, α^∨⟩`. This module
assembles the blocks `gam m` of `WeylModule` along the `α`-strings of a finite family of weights
`ω : C → X`. The result is an integral representation of `2 × 2` matrices on `ℤ^C` whose
raising and lowering operators move weights by `±α`.

## String decompositions

`StringDecomp α pair C ω` is a structure consisting of:

- a finite index type `K` of strings and lengths `len k ≤ 3`;
- an equivalence `eqv : C ≃ Σ k : K, Fin (len k + 1)`;
- `weight_eq`: the `k`-th block is the unbroken string `ω k₀, ω k₀ + α, …, ω k₀ + len k • α`,
  where `k₀ = eqv.symm ⟨k, 0⟩`;
- `pair_bot`: the bottom weight pairs to `−len k`.

For such `S`:

- `S.rep g`, `S.E k`, `S.F k` are the block-diagonal matrices of `gam (len k) g`,
  `gamE (len k) k` and `gamF (len k) k`, transported to `C` along `eqv` (`submatrix`).
- `rep_mul`, `rep_one`, `rep_map`, `E_zero`, `F_zero`, `E_mul`, `F_mul`, `E_eq_zero`,
  `F_eq_zero` (for `k > 3`), `rep_upper`, `rep_lower`: the blockwise statements of
  `WeylModule`, transported with `blockDiagonal'_mul` and `submatrix_mul_equiv`.
- `weight_symm`, `weight_apply`, and `pair_apply`: if `pair α = 2`, then the `j`-th member of
  the `k`-th string pairs to `2j − len k`.
- `exists_of_blockDiagonal'_ne_zero`: a nonzero entry of a block-diagonal matrix lies in a
  diagonal block.
- `E_ne_zero`, `F_ne_zero`: a nonzero entry of `E^[k]` (row `r`, column `c`) has
  `ω r = ω c + k • α`, and a nonzero entry of `F^[k]` has `ω r + k • α = ω c`.
- `rep_weyl_ne_zero`: if `pair α = 2`, then a nonzero entry of `rep [[0, 1], [−1, 0]]` has
  `ω r = ω c − pair (ω c) • α`, which is the reflection of `ω c`.
- `rep_diag`, and `rep_diag_units`: if `pair α = 2`, then `rep diag(t, t⁻¹)` is the diagonal
  matrix with entries `t^(pair (ω d))`.
- `E_one_mul_F_one_sub`: if `pair α = 2`, then `[E, F]` is the diagonal matrix of the pairings
  `pair (ω d)`.
- `E_apply`, `F_apply`: explicit entries. `E^[k]` has entry `C(j_r, k)` at `(r, c)` when `r`
  and `c` lie in the same string and `j_c + k = j_r`, and `F^[k]` has entry
  `C(len − j_r, k)` when `j_r + k = j_c`. Here `j_d = (eqv d).2` is the position in the string.

### Sums and sigma types

- `sum S₁ S₂` decomposes the family `Sum.elim ω₁ ω₂` on `C₁ ⊕ C₂`, and `sigma T` decomposes
  `fun d => ν d.1 d.2` on `Σ w, D w`. The lemmas `sum_len_inl`, `sum_len_inr`, `sum_eqv_inl`,
  `sum_eqv_inr`, `sigma_len` and `sigma_eqv` compute their fields. The lemmas `sum_E`, `sum_F`,
  `sigma_E` and `sigma_F` show that the operators are `fromBlocks (S₁.E k) 0 0 (S₂.E k)` and
  `blockDiagonal' (fun w => (T w).E k)`. The proofs compare entries through `E_apply` and
  `F_apply`, using the helper `ite_and_congr_of_injective`, which rewrites an injective
  equation inside an `if` regardless of the decidability instance.

## String decompositions from unbroken strings

`StringData α pair C ω` records, for a family with injective weight map, numbers `bot d` and
`top d` of steps down and up from `ω d` along `α` within the family. The field `exists_iff` says
that `ω d + z • α` occurs in the family exactly for `−bot d ≤ z ≤ top d`, the field
`bot_add_top_le` says `bot d + top d ≤ 3`, and the field `pair_eq` says
`pair (ω d) = bot d − top d`.

- `bot_top_of_eq`, `mate`, `weight_mate`, `bottom`, `weight_bottom`, `bot_bottom`,
  `top_bottom`, `eq_add_smul_iff`: `mate d z` is the member of weight `ω d + z • α` (chosen
  with `Classical.choose`), and `bottom d` is the bottom of the string through `d`.
- `decomp`: the string decomposition with `K = {d // bot d = 0}`, `len k = top k`, and
  `eqv d = ⟨bottom d, bot d⟩`. The lemmas `decomp_eqv_fst`, `decomp_eqv_snd` and
  `decomp_len` compute it.
- `decomp_E_one`: `E` sends `ω c` to `ω c + α` with coefficient `bot r`, where `r` is the
  member of weight `ω c + α`. `decomp_F_one`: `F` sends `ω c` to `ω c − α` with coefficient
  `top r`, where `r` is the member of weight `ω c − α`.

## Provenance

This is the standard decomposition of a finite-dimensional `SL₂`-module into irreducible
summands along root strings (Humphreys, *Introduction to Lie Algebras and Representation
Theory*, §7.2; Steinberg, *Lectures on Chevalley groups*, §2). Here it is used in the converse
direction: the representation is built from a combinatorial string decomposition of a set of
weights. The packaging into `StringDecomp` and `StringData` is internal to this project.
