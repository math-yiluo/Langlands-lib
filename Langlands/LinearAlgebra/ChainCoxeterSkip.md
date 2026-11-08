# The modified chain in path indexing

This module is pure linear algebra over an arbitrary commutative ring `R`. It restates the
determinant of the modified chain from `LinearAlgebra.ChainCoxeterMinors` in the indexing of a
single chain `Fin (L + 1)`, for example the lines of a type `A_L` path in the order of the path.
The middle vertex is `i + 1`, and the merged edge skips it, joining `i` to `i + 2`. The module
also adds change-of-basis lemmas, so that a matrix acting on another index type through a basis
can be brought into this indexing. It is an internal prerequisite for the `N'''` half of
Steinberg's Corollary 9.18 in the even type `A` case of the quasi-split Steinberg quotient task.

## Definitions

- `skipEquiv hi`, for `hi : i + 2 ≤ L`: the equivalence
  `(Fin (i + 1) ⊕ Fin (L - i - 2 + 1)) ⊕ Unit ≃ Fin (L + 1)`. It sends `inl (inl a)` to `a`,
  `inl (inr b)` to `i + 2 + b`, and `inr ()` to `i + 1`. `skipLeft`, `skipRight` and `skipOuter`
  are its restrictions to the left vertices `0, …, i`, the right vertices `i + 2, …, L` and their
  union.
- `IsSkipFactor hi g lam mu`, for `g : Matrix (Fin (L + 1)) (Fin (L + 1)) R`, says:
  - every column other than `i` and `i + 2` is the corresponding column of the identity;
  - column `i + 2` is `lam • e_i`;
  - column `i` vanishes outside rows `i` and `i + 2`, and has entry `mu` in row `i + 2`.
- `IsChainListSkip i l F E a b`: as `IsChainList` of `ChainCoxeterMinors`, for chain factors of
  `Fin (L + 1)` with edges `Fin L`. Every edge other than `i` and `i + 1` occurs exactly once, the
  edges `i` and `i + 1` do not occur, and the other members of the list are identities.
- `leftEdge` and `rightEdge`: the edge assignments of the left and right chains, the latter
  renumbered from `0`.

## Results

- `IsChainFactor.submatrix_of_embedding`: restricting a chain factor along an injective vertex
  map that carries an edge `j'` to the edge `j` gives a chain factor at `j'` with the same
  scalars. `IsChainFactor.submatrix_eq_one`: restricting it to vertices avoiding its edge gives
  the identity. `IsChainFactor.apply_of_not_mem`: entries outside the two moved vertices are those
  of the identity.
- `submatrix_skipEquiv_of_left`, `submatrix_skipEquiv_of_right` and
  `submatrix_skipEquiv_of_outer`: a matrix agreeing with the identity outside the left block,
  outside the right block, or on the row and column of the middle vertex, becomes a block matrix
  in the indexing of `skipEquiv`. `submatrix_skipEquiv_prod` does the same for list products.
- `IsSkipFactor.apply_of_middle`, `IsSkipFactor.submatrix_skipEquiv` and
  `IsSkipFactor.isMergedFactor`: a skip factor fixes the middle vertex, and on the outer vertices
  it is a merged factor (`IsMergedFactor`) of the left and right chains.
- `IsChainListSkip.edge_ne`, `IsChainListSkip.submatrix_skipEquiv`,
  `IsChainListSkip.isChainList_left` and `IsChainListSkip.isChainList_right`: a skip chain list
  is block diagonal, and its left and right blocks are chain lists of the left and right chains.
- `det_one_sub_skipChain` (**the modified chain in path indexing**): let `g` be a skip factor
  with scalar `mu` and `R = (l.map F).prod` a skip chain list. Suppose the scalars of the edges
  below `i` are units. Then
  `det (1 - (1 + cb E_{i+1, i+2}) (1 + ca E_{i, i+1}) (g R)) = -(ca * cb * mu * ∏_{j < i} a_j * b_j)`.
- `det_one_sub_conj`: for rectangular `P : Matrix d V R` and `Q : Matrix V d R` with `P Q = 1`
  and `Q P = 1`, `det (1 - M) = det (1 - Q M P)`. `conj_mul` and `conj_list_prod`: the change of
  basis is multiplicative. `conj_eq_of_mulVec` and `conj_apply_of_mulVec`: if `M` sends column
  `c` of `P` to `∑_w coef w • (column w of P)`, then column `c` of `Q M P` is `coef`.
- `submatrix_one_add_smul_single`: reindexing `1 + c • E_{m, r}` along an equivalence.

## Proof as implemented

`skipEquiv` is defined by its values on the three summands and by a case split on the value for
the inverse. The block lemmas compare entries in the nine pairs of summands. Outside the relevant
block both sides are entries of the identity, by injectivity of `skipEquiv`. List products use
Mathlib's `submatrix_mul_equiv` and `fromBlocks_multiply`. The edge transfers follow the entries of
the `IsChainFactor` fields through the vertex embeddings. A chain list of the skip chain has no
member at the edges `i` and `i + 1`, by `countP_eq_zero`, so every factor lives in the left or the
right block. The main theorem reindexes along `skipEquiv` (`det_submatrix_equiv_self`).
`submatrix_single_equiv` and the values of `skipEquiv.symm` at `i`, `i + 1`, `i + 2` move the
unipotent factor. The theorem then applies `det_one_sub_unipotent_mul_mergedChain`.

For the change of basis, `M = P (Q M P) Q` because `P Q = 1`. Mathlib's `det_one_sub_mul_comm`,
which allows rectangular factors, together with `Q P = 1` gives `det (1 - M) = det (1 - Q M P)`.

## Provenance and scope

This is an internal module and formalizes no source statement. It is the indexing step between
`ChainCoxeterMinors` and the matrices of Steinberg's `N'''` (Steinberg 1965, §9.11) in a basis of
path lines. It does not mention groups or representations.
