# Path Coxeter products in any order, and the pattern block

This module is pure algebra over an arbitrary commutative ring `R`, in the namespace
`Langlands.LinearAlgebra.PathCoxeter`. It imports `Langlands.LinearAlgebra.PathCoxeterCoordinates`,
which in turn imports `Langlands.LinearAlgebra.PathCoxeterCharpoly`. The earlier modules compute
characteristic polynomials of path products taken in the standard order. This module provides
the pieces needed to apply them to actual products of group elements:

- products taken in an arbitrary order, where some factors are `1`;
- the explicit `3 × 3` block of Steinberg's pattern element `u_b u_a x_α(s) n_α α^∨(t)` on a
  path representation;
- congruence and ring-hom lemmas for the coordinates `patCoord` and the polynomial `ordPoly`.

The module is an internal prerequisite of the split even-path cross-section task
(`Langlands.GroupScheme.SplitEvenChainCrossSectionStatement`, Steinberg 1965, §9.15–9.19).

**Provenance: internal.** The module has no counterpart in the literature. Steinberg's §9 proves
the cross-section by other means, and these formulas were derived for this project. Every result
is stated in full below and proved in Lean.

Notation from the earlier modules: `sfac n i c` is the simple factor on the lines `i, i+1` of
`R^n`, `core n j β` is the matrix acting by the `3 × 3` block `β` on the lines `j, j+1, j+2`
and as the identity elsewhere, `pprod n a k c` is the ordered product of the simple factors
`sfac n (a+i) (c (a+i))` for `i < k`, and `pathMat k c β = pprod 0 k c * core k β *
pprod (k+2) k c` on `2k + 3` lines. `vget v j` is the `j`-th entry of `v` (`0` for `j ≥ n`).

## Definitions

- `patY n k c β i`: the `i`-th factor of a path product with a block. It is `sfac n i (c i)`
  for `i < k`, `core n k β` for `i = k`, `sfac n (i+1) (c (i+1))` for `k < i ≤ 2k`, and `1`
  for `i > 2k`.
- `ordY n k c i`: the `i`-th factor of an ordinary path product. It is `sfac n i (c i)` for
  `i ≤ 2k+1`, and `1` beyond.
- `endpointMat n i l a b`: the matrix whose column `i` is `a e_l`, whose column `l` is `b e_i`,
  and whose other columns are those of the identity.
- `torusMat n i τ τ'`: the diagonal matrix with entry `τ` at line `i`, `τ'` at line `i + 2`,
  and `1` elsewhere.
- `blockBeta τ τ' a b x ca cb`: the `3 × 3` block (rows `r`, columns `s`, indexed from `0`;
  every other entry is `0`)

  | `r \ s` | `0` | `1` | `2` |
  |---|---|---|---|
  | `0` | `τ x a` | `ca` | `b τ'` |
  | `1` | `τ a cb` | `1` | `0` |
  | `2` | `τ a` | `0` | `0` |

## Results

**Products with trivial factors removed.**

- `list_prod_map_eq_filterMap`: in a monoid, let `f a = 1` when `idx a = none` and
  `f a = y i` when `idx a = some i`. Then for every list `l`,
  `(l.map f).prod = ((l.filterMap idx).map y).prod`.
- `perm_range_of_nodup`: a duplicate-free list of natural numbers whose members are exactly the
  numbers below `N` is a permutation of `List.range N`.

**Products in any order.** Assume `n = 2k + 3`.

- `patY_commute`, `ordY_commute`: factors with indices `i + 2 ≤ j` commute.
- `prod_range_patY`: the product of `patY (2k+3) k c β i` over `i = 0, …, 2k` in increasing
  order is `pathMat k c β`.
- `prod_range_ordY`: the product of `ordY (2k+3) k c i` over `i = 0, …, 2k+1` in increasing
  order is `pprod (2k+3) 0 (2k+2) c`.
- **`charpoly_prod_patY`**: for every list `l` that is a permutation of `List.range (2k+1)`,
  the product of `patY n k c β i` over `i ∈ l`, in the order of `l`, has the characteristic
  polynomial of `pathMat k c β`.
- **`charpoly_prod_ordY`**: for every list `l` that is a permutation of `List.range (2k+2)`,
  the product of `ordY n k c i` over `i ∈ l` has characteristic polynomial `ordPoly k c`.

**The pattern block.**

- `vget_one_add_single_mulVec`: `(1 + E_ij c) v` has entries `v_s + [s = i] c v_j`.
- `vget_endpointMat_mulVec` (`i ≠ l`, both `< n`): `endpointMat n i l a b * v` has entry
  `a v_i` at `l`, `b v_l` at `i`, and `v_s` at every other `s`.
- `vget_torusMat_mulVec`: `torusMat n i τ τ' * v` has entry `τ v_i` at `i`, `τ' v_(i+2)` at
  `i + 2`, and `v_s` at every other `s`.
- **`block_eq_core`** (`i + 3 ≤ n`): write `E_pq c` for the matrix with the single entry `c`
  at `(p, q)`. Then

  `(1 + E_(i+1, i+2) cb) (1 + E_(i, i+1) ca) (1 + E_(i, i+2) x) endpointMat n i (i+2) a b
  torusMat n i τ τ' = core n i (blockBeta τ τ' a b x ca cb)`.

- **`block_eq_core_false`** (`i + 3 ≤ n`):
  `(1 + E_(i, i+2) x) endpointMat n i (i+2) a b = core n i (blockBeta 1 1 a b x 0 0)`.

**Coordinates depend only on the relevant values.**

- `patCoord_congr`: if `d i = d' i` for `i < k` and for `k + 2 ≤ i ≤ 2k + 1`, then
  `patCoord k d σ δ j = patCoord k d' σ δ j` for every `j`.
- `patCoord_map`: a ring hom `φ` commutes with `patCoord`:
  `φ (patCoord k d σ δ j) = patCoord k (φ ∘ d) (φ σ) (φ δ) j`.
- `ordPoly_congr`: if `γ j = γ' j` for `j < 2k + 2`, then `ordPoly k γ = ordPoly k γ'`.

## Proof as implemented

`list_prod_map_eq_filterMap` is an induction on the list, with a case split on `idx a`.
`perm_range_of_nodup` is `List.perm_ext_iff_of_nodup`.

The commutation lemmas unfold `patY` and `ordY` and use the commutation lemmas of the first
module (`sfac_commute_sfac`, `sfac_commute_core`, `core_commute_sfac`) on the line indices,
which are disjoint because `i + 2 ≤ j`; factors equal to `1` commute with everything.
`prod_range_patY` splits `range (2k+1)` as `range k ++ [k] ++ (k + 1 + range k)` and evaluates
each factor. `prod_range_ordY` evaluates each factor. The order-independence statements are
then the tree lemma `charpoly_prod_perm` of the first module, together with
`charpoly_pprod_eq_ordPoly` for ordinary products.

The action lemmas compute the matrix-vector products entrywise: in each case one summand of the
matrix product survives (`Fintype.sum_eq_single`). `block_eq_core` compares the two matrices by
their action on vectors (`ext_iff_mulVec`, `vget_injective`): the left side acts by the
composite of the five action lemmas, the right side by `coreAct` (`vget_core_mulVec`), and the
entries agree on the lines `i, i+1, i+2` by `simp` and `ring` and are unchanged elsewhere.
`block_eq_core_false` is `block_eq_core` with `τ = τ' = 1`, `ca = cb = 0`, since then the two
unipotent factors and `torusMat n i 1 1` are the identity.

`patCoord_congr` and `patCoord_map` unfold `patU` and `patCoord` by cases. `ordPoly_congr`
rewrites the sum termwise.
