# Reciprocal characteristic polynomials of weighted permutation matrices

Module `Langlands.Galois.HeckeInduction.MonomialDeterminant`, name space
`Langlands.MonomialDeterminant`. It is elementary linear algebra over an arbitrary commutative
ring `R`, used to compute Euler polynomials of finite-index inductions of characters.

## Declarations

- `cycleShift d : Matrix (Fin m) (Fin m) R`, for `d : Fin m → R`, is the weighted cyclic shift:
  row `k` has the entry `d k` in column `finRotate m k` (that is `k + 1` modulo `m`) and zeros
  elsewhere (`cycleShift_apply`).
- `det_one_sub_X_smul_cycleShift (hm : 0 < m) d` :
  `det (1 - X • (cycleShift d).map C) = 1 - C (∏ k, d k) * X ^ m` in `R[X]`;
  `det_one_sub_X_smul_cycleShift_succ` is the same identity written for `m = n + 1`.
- `val_finRotate k : (finRotate m k : ℕ) = (k + 1) % m`.
- `det_one_sub_X_smul_monomial π c base len hlen hcycle hbij`. Let `Q` and `W` be finite types,
  `π : Q → Q`, `c : Q → R`, `base : W → Q` and `len : W → ℕ` with `0 < len w`,
  `π^[len w] (base w) = base w`, and the map `(Σ w, Fin (len w)) → Q`,
  `⟨w, k⟩ ↦ π^[k] (base w)`, bijective. For the matrix `M` with
  `M q q' = if π q = q' then c q else 0`, the theorem states
  `det (1 - X • M.map C) = ∏ w, (1 - C (∏ k : Fin (len w), c (π^[k] (base w))) * X ^ len w)`.

The hypotheses say that the orbits of `π` are the cycles through the points `base w`, of lengths
`len w`, each listed once; `M` is then a weighted permutation matrix and the formula is the
product, over the cycles, of `1 - (product of the weights on the cycle) X ^ (length)`.

## Proofs

`det_one_sub_X_smul_cycleShift_succ`: for `m = 1` the matrix is `1 - X d 0`. For `m = n + 2`,
Laplace expansion along the last row (`Matrix.det_succ_row`) has two nonzero terms. The entry in
the last column is `1`, and its minor is upper triangular with diagonal entries `1`
(`Matrix.det_of_isUpperTriangular`). The entry in the first column is `-X d (last)`, and its minor
is lower triangular with diagonal entries `-X d k` for `k` in the first `n + 1` positions
(`Matrix.det_of_isLowerTriangular`). With `P` the product of `d` over the first `n + 1`
positions, the two terms give
`1 + (-1)^(n+1) (-X d (last)) (-X)^(n+1) P = 1 - X^(n+2) P d (last)`.

`det_one_sub_X_smul_monomial`: reindex `Q` by `Σ w, Fin (len w)` through the given bijection
(`Matrix.det_submatrix_equiv_self`). Then `π` becomes `⟨w, k⟩ ↦ ⟨w, finRotate _ k⟩`, because
`π^[k+1] (base w) = π^[(k+1) % len w] (base w)` by periodicity. So the reindexed matrix
vanishes outside the diagonal blocks and is block triangular for the first coordinate (with a
linear order on `W` transported from `Fintype.equivFin`). `Matrix.BlockTriangular.det`
expresses the determinant as the product of the determinants of the diagonal blocks, every
block being nonempty. Each block, reindexed by `Fin (len w)` through `Equiv.sigmaSubtype`, is
`1 - X • (cycleShift (fun k => c (π^[k] (base w)))).map C`, and the single-cycle case applies.

## Provenance

This is a derived, internal result. The identity is the classical computation of the
characteristic polynomial of a monomial matrix cycle by cycle. The module follows no particular
source; the implemented proof is described above.
