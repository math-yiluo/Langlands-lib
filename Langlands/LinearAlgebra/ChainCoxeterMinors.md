# Two minors of products of chain factors

This module is pure linear algebra over an arbitrary commutative ring `R`. It computes certain
minors and determinants of products of "chain factors". Chain factors are matrices that move only
two neighbouring basis vectors of a chain, and they may be multiplied in any order. The module is
an internal prerequisite for the even type `A` case of the quasi-split Steinberg quotient task. In
the normalized path basis of `Rational.PathReflectionScalars`, a simple root element times its
canonical representative is such a factor. The final theorem gives the value of `det (1 - M)` for
the matrix shape of Steinberg's `N'''` (Steinberg 1965, §9.11). The group-theoretic application is
not part of this module.

## Definitions

All matrices are `Matrix ι ι R` for the index types below.

- `IsChainFactor g j a b`: for `g : Matrix (Fin (r + 1)) (Fin (r + 1)) R` and an edge
  `j : Fin r`, the columns of `g` are as follows. Every column other than `j.castSucc` and
  `j.succ` is the corresponding column of the identity. Column `j.succ` is `a • e_{j.castSucc}`.
  Column `j.castSucc` vanishes outside rows `j.castSucc` and `j.succ`, and has entry `b` in row
  `j.succ`. Its diagonal entry is arbitrary.
- `IsChainList l F E a b`: for a list `l : List ι`, factors `F : ι → Matrix _ _ R` and an
  assignment `E : ι → Option (Fin r)` of edges, every member `i` of `l` with `E i = none` has
  `F i = 1`. Every member with `E i = some j` is a chain factor at `j` with scalars `a j` and
  `b j`. Every edge `j` occurs exactly once (`l.countP (E · = some j) = 1`). The product
  `(l.map F).prod` is then a product of one chain factor for each edge, in an arbitrary order,
  with identity factors interspersed.
- `FixesVertex X p`: `X` fixes `e_p` and preserves the span of the other basis vectors, that is,
  `X p p = 1` and the other entries of row and column `p` vanish.
- `predEdge` and `castPredEdge`: renumber the edges of `Option (Fin (r + 1))` after deleting the
  bottom or the top edge.
- `IsMergedFactor g lam mu`: for `g` indexed by `Fin (p + 1) ⊕ Fin (q + 1)`, the same column
  conditions as a chain factor. The two moved vectors are the top vertex `inl (last p)` of the
  left chain and the bottom vertex `inr 0` of the right chain. Column `inr 0` is
  `lam • e_{inl (last p)}`, and column `inl (last p)` has entry `mu` in row `inr 0`.

## Results

- `fixesVertex_one`, `FixesVertex.mul`, `fixesVertex_prod`: closure properties.
  `submatrix_mul_of_col`, `submatrix_mul_of_row`, `submatrix_prod` and the `Fin.succ` and
  `Fin.castSucc` variants: deleting a fixed vertex commutes with products.
  `FixesVertex.det_eq`: the determinant equals that of the matrix with the fixed vertex deleted.
  `FixesVertex.commute_proj`: such a matrix commutes with `1 - E_pp`.
- `IsChainFactor.fixesVertex`, `IsChainFactor.submatrix_succ`, `IsChainFactor.submatrix_castSucc`
  and `IsChainFactor.submatrix_succ_of_zero`: behaviour under deleting a vertex. The last says
  that deleting the bottom vertex from the factor of the bottom edge gives `1 - E_00`.
- `IsChainFactor.det_eq`: `det g = -(a * b)`.
- `det_one_sub_proj_mul`: `det (1 - (1 - E_00) Z)` is the minor of `1 - Z` obtained by deleting row
  and column `0`.
- `det_proj_sub_mul_of_top`: for a chain factor `g` at the top edge and `Z` fixing the top
  vertex, `det ((1 - E_top) - g Z) = a * b * det (1 - Z' - E_top')`. Here `Z'` deletes the top
  vertex.
- `IsChainList.exists_split`, `IsChainList.restrict_succ` and `IsChainList.restrict_castSucc`:
  split the list at the factor of the bottom or top edge, and pass to the shorter chain.
- `det_submatrix_succ_one_sub_prod` (**bottom minor**): for every chain list,
  `det ((1 - R).submatrix Fin.succ Fin.succ) = 1`, where `R = (l.map F).prod`.
- `det_one_sub_prod_sub_single_last` (**top corner**): if all `a j` and `b j` are units, then
  `det (1 - R - E_{last, last}) = -∏ j, a j * b j`.
- `updateRow_sub_single` and `submatrix_one_sub`: two small identities.
  `isUnit_det_prod`: a list product of matrices with unit determinants has unit determinant.
- `adjugate_one_sub_mergedFactor_mul` (**merged cofactor**): for a merged factor `g` and
  block-diagonal `T = fromBlocks RL 0 0 RR`,
  `adjugate (1 - g T) (inr 0) (inl (last p)) = -(mu * det (1 - RL - E_last) * det ((1 - RR)'))`,
  where `(1 - RR)'` deletes the bottom row and column.
- `det_one_sub_unipotent_mul_fromBlocks` (**middle vertex**): for any finite `W`, `Q` on `W`, and
  distinct `z0`, `lt` in `W`, on `W ⊕ Unit` with middle vertex `inr ()`,
  `det (1 - (1 + cb E_{mid, z0}) (1 + ca E_{lt, mid}) (Q ⊕ 1)) = -(ca * cb * adjugate (1 - Q) z0 lt)`.
- `det_one_sub_unipotent_mul_mergedChain` (**the modified chain**): let
  `V = (Fin (p + 1) ⊕ Fin (q + 1)) ⊕ Unit`. Let `RL` and `RR` be chain-list products on the left
  and right chains, with left scalars units, and let `g` be a merged factor with scalar `mu`. Then
  `det (1 - (1 + cb E_{mid, inr 0}) (1 + ca E_{inl last, mid}) ((g (RL ⊕ RR)) ⊕ 1))` equals
  `-(ca * cb * mu * ∏ j, aL j * bL j)`. It is independent of the orders of both chain products,
  of the diagonal entries of all factors, of `lam` and of the right-chain scalars.

## Proof as implemented

**Bottom minor**, by induction on the number of edges. Split the list at the factor `g₀` of the
bottom edge, so that `R = A g₀ B`. All other factors fix the bottom vertex. Deleting that vertex
therefore commutes with the products, and turns `g₀` into `1 - E_00`. Mathlib's
`det_one_sub_mul_comm` (Sylvester's identity) rotates `A' (1 - E_00) B'` into `(1 - E_00) B'A'`.
`det_one_sub_proj_mul` turns this into the bottom minor of `1 - B'A'`, where `B'A'` is a chain
product of the shorter chain in the rotated order.

**Top corner**, by induction. Split at the factor `g` of the top edge, `R = A g B`. Each chain
factor has unit determinant `-(a * b)`, so `A` is invertible. `A` commutes with `1 - E_top`
because it fixes the top vertex. So `det ((1 - E_top) - A g B) = det ((1 - E_top) - g B A)`, by
Mathlib's `det_conj`. Expanding this along the top column (`det_succ_column`) leaves a single
entry `-a`. The resulting minor is the matrix `1 - Z'` with its last row replaced by `-b` times the
last row of `Z'`. Linearity in that row (`det_updateRow_smul`, `updateRow_sub_single`) gives
`b * det (1 - Z' - E_top')`, and the induction hypothesis applies to the rotated shorter chain.

**Merged cofactor.** `adjugate_apply` writes the cofactor as the determinant of `1 - g T` with
row `inl last` replaced by `e_{inr 0}`. Row `inr 0` of `1 - g T` is `e_{inr 0} - mu • T_{inl last}`.
Subtracting the replaced row (`det_updateRow_add_smul_self`) leaves `-mu • T_{inl last}`. Swapping
the two rows (`det_permute`, sign `-1`) produces a block-diagonal matrix (`det_fromBlocks_zero₂₁`).
Its left block is `1 - RL` with the last row replaced by `-mu • RL_last`, of determinant
`mu * det (1 - RL - E_last)`. Its right block is `1 - RR` with row `0` replaced by `e_0`, of
determinant the bottom minor (`adjugate_fin_succ_eq_det_submatrix`).

**Middle vertex.** The column of the middle vertex of `1 - U (Q ⊕ 1)` has the single entry `-ca`
in row `lt`. Expanding along it (`det_eq_sum_mul_adjugate_col`, `adjugate_apply`) and swapping the
rows `lt` and `mid` gives a block matrix with blocks `1` and `1 - Q`, where row `lt` is replaced by
`-cb • Q_{z0}`. Writing `Q_{z0} = e_{z0} - (1 - Q)_{z0}`, linearity in that row gives
`adjugate (1 - Q) z0 lt`. The other term vanishes because two rows are equal (`det_zero_of_row_eq`).

The modified-chain theorem combines the middle-vertex, merged-cofactor, top-corner and
bottom-minor results.

## Provenance and scope

This is an internal module and formalizes no source statement. It supplies the matrix computation
behind the `N'''` half of Steinberg's Corollary 9.18 (Robert Steinberg, *Regular elements of
semi-simple algebraic groups*, 1965). That half says that in the standard representation of
`SL(n + 1)` the elements of `N'''` do not have `1` as a characteristic value. In the intended
application the chain is the path of a type `A_{2m}` component. The left and right chains are the
lines on either side of the middle line. The merged factor is `x_α(s) n_α α^∨(t)` with
`α = α_m + α_{m+1}`, and the unipotent factor is `u_b u_a`. Steinberg's own proof goes through
characters (9.15–9.16), whereas this one is a direct determinant computation. The module does not
identify any of these matrices with group elements.
