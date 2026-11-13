# Darboux matrices adapted to a Witt block decomposition

Lean module: `Langlands.GroupScheme.Quaternionic.DegreeSplittingDarboux`
(namespace `Langlands.GroupScheme.Quaternionic.DegreeSplitting`).

Setting: `D` a division algebra, finite-dimensional over a field `K`, with an involution of the
first kind `σ` whose symmetric elements have dimension `δ (δ + 1) / 2`; a matrix chart
`e : L ⊗[K] D ≃ₐ[L] M_δ(L)` over a field extension `L` (index type `Fin δ`); `S` the involution
matrix of `DegreeSplittingChart`, symmetric by `involutionMatrix_transpose`. This internal
module builds the Darboux matrices of the split alternating form that are adapted to a Witt
decomposition. `DegreeSplittingTorus` uses them to put the Witt torus inside the diagonal torus
of `Sp_{2N}`.

## Definitions and auxiliary facts

* `splitGram_apply`: the `((i, a), (j, b))` entry of `splitGram e σ G` is the `(a, b)` entry of
  `e(1 ⊗ G_{ij}) S` (for any finite index type in place of `Fin δ`).
* `wittWeight : (Fin r ⊕ Fin r) ⊕ Fin d → Fin r → ℤ` is `e_k` on `inl (inl k)`, `-e_k` on
  `inl (inr k)` and `0` on `inr _`: the weights of the Witt torus on Witt coordinates.
* `blockWeight δ r a`, for `a : Fin N`, is the vector whose `k`-th entry is `1` if
  `k δ ≤ a < (k + 1) δ` and `0` otherwise: the indicator of the `k`-th block of size `δ`.
* `darbouxWeight δ r : Fin N ⊕ Fin N → Fin r → ℤ` is `blockWeight δ r a` on `inl a` and
  `-blockWeight δ r a` on `inr a`.
* `block_iff`: for `c < δ`, `l δ ≤ c + δ k < (l + 1) δ ↔ l = k`.
  `blockWeight_eq_single`: if `a = c + δ k` with `c < δ`, then `blockWeight δ r a = e_k`.
  `blockWeight_eq_zero`: if `r δ ≤ a`, then `blockWeight δ r a = 0`.

## Main result

`exists_wittDarboux hσ ε hHU hu hH' hN`: let `ε : Fin m ≃ (Fin r ⊕ Fin r) ⊕ Fin d`,
`H' ∈ M_m(D)` a unit, and `HU ∈ M_d(D)` trace-valued `σ`-antihermitian, with
`H' i j = wittGram HU (ε i) (ε j)` for all `i, j` (`wittGram` from `AntihermitianWittBlock`).
Let `m δ = 2 N`. Then `r δ ≤ N`, and there are matrices
`P : M_{(Fin N ⊕ Fin N) × (Fin m × Fin δ)}(L)` and `P' : M_{(Fin m × Fin δ) × (Fin N ⊕ Fin N)}(L)`
with

* `P P' = 1` and `P' P = 1`;
* `P C Pᵀ = J (Fin N) L` for `C = splitGram e σ H'`;
* homogeneity: `P α β ≠ 0 → darbouxWeight δ r α = wittWeight (ε β.1)`.

## Proof

1. **Block form of `C`.** Reorder the columns `Fin m × Fin δ` by `ε` into
   `((Fin δ × Fin r) ⊕ (Fin δ × Fin r)) ⊕ (Fin d × Fin δ)` (`colE`). By `splitGram_apply` and the
   block form of `H'`, `C` becomes `C0 = [[0, Y, 0], [-Y, 0, 0], [0, 0, C_U]]`, where
   `Y = blockDiagonal (fun _ => S)` and `C_U = splitGram e σ HU`. Here `e(1 ⊗ 1) = 1` and
   `e(1 ⊗ -1) = -1`.
2. **Anisotropic part.** `det C ≠ 0` (`det_splitGram_ne_zero`), and
   `det C0 = det [[0, Y], [-Y, 0]] · det C_U` (`det_fromBlocks_zero₂₁`), so `det C_U ≠ 0`. `C_U`
   is alternating (`transpose_splitGram`, `splitGram_diag`). The Library's
   `SymplecticMatrix.exists_mul_mul_transpose_eq_J` gives `k0` and `P_U`, `P_U'` with
   `P_U P_U' = 1`, `P_U' P_U = 1` and `P_U C_U P_Uᵀ = J (Fin k0)`. Comparing ranks
   (`rank_one`, `rank_mul_le_left`, `rank_le_card_width`) gives `2 k0 = d δ`. With
   `m = 2r + d` this gives `N = r δ + k0`, so `r δ ≤ N`.
3. **Hyperbolic part.** Let `Q = -S⁻¹` and `Q2 = blockDiagonal (fun _ => Q)`. Since `Sᵀ = S`,
   `Q S = -1` and `S Qᵀ = -1`, so `Y Q2ᵀ = -1` and `Q2 Y = -1`. With
   `P0 = [[1, 0, 0], [0, Q2, 0], [0, 0, P_U]]`, block multiplication gives
   `P0 C0 P0ᵀ = diag(J (Fin δ × Fin r), J (Fin k0))`.
4. **Rows.** `eA : (Fin δ × Fin r) ⊕ Fin k0 ≃ Fin N` sends `inl (c, k)` to `c + δ k` and
   `inr b` to `r δ + b` (`finProdFinEquiv`, `finSumFinEquiv`). Reindexing the rows by `eA`
   (`rowE`) turns `diag(J, J)` into `J (Fin N)`. Put `P = P0` reindexed by `rowE` and `colE`.
   Then `P C Pᵀ = J`.
5. **Inverse.** `P' = C Pᵀ (-J)`. Then `P P' = (P C Pᵀ)(-J) = -J² = 1`. Since the index types have
   the same cardinality, `mul_eq_one_comm_of_equiv` gives `P' P = 1`.
6. **Homogeneity.** `P0` is homogeneous for the weights `e_k`, `-e_k`, `0` on rows and columns:
   the nonzero entries of the identity block and of `Q2` lie on the block diagonal, and `P_U`
   has weight `0` on both sides. On rows, `blockWeight_eq_single` and `blockWeight_eq_zero`
   identify `darbouxWeight` with these weights through `eA`. On columns, `wittWeight ∘ ε`
   matches them through `colE`.

## Provenance

This is the explicit form of the standard fact that over a splitting field a Witt
decomposition of the antihermitian form gives a symplectic basis in which the maximal split
torus of `SU(D, h)` acts diagonally, each hyperbolic pair contributing `δ` diagonal
coordinates (Tits 1966, Table II, type `C_n`). The construction was written for this module.
It uses the Library's Darboux theorem `SymplecticMatrix.exists_mul_mul_transpose_eq_J` and
Mathlib's block-matrix lemmas.
