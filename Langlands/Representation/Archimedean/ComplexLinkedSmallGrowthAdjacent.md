# Small growth for an adjacent linked pair

## Main result

`AdjacentGrowth.smallGrowth_adjacent`: let `χ_k(z) = phase(z)^{l_k} |z|^{2 t_k}` for all `k`, and
let `i + 1 < n` and `p, q ≥ 1` with `l_{i+1} - l_i = p - q` and `t_{i+1} - t_i = (p + q)/2`
(equivalently `χ_{i+1}(z) = χ_i(z) z^p z̄^q`). Then `SmallGrowth n χ` holds.

## Construction

- Level data: `e_m = l_m - l_{m-1}` (`l_{-1} = 0`, via `shift`), `τ_k = t_k + (n-1)/2 - k`,
  `dτ_m = τ_m - τ_{m-1}`; `h_m = e_m⁺`, `b_m = e_m⁻` except at `m = r = i + 1`, where
  `h_r = p - 1`, `b_r = q - 1`. Then `h_m - b_m = e_m` for all `m`, the sums telescope
  (`sum_filter_le_eq`, `sum_range_sub_shift`) and the Gram exponent of level `r` is `0`.
- `E` is `levelSpan h b dτ` viewed inside the `U(n)`-finite functions
  (`levelSpan_le_kFiniteFunctions`): nonzero (`levelProduct_tailSelect_one`), finite-dimensional
  and `U(n)`-stable.
- `gramWeight m v = tailGram m (nbMat v)`: degree `≤ 2n` (`gramWeight_mem_degLE`) and positive
  real (`isPosReal_gramWeight`); `gramExp m = dτ_m - (h_m + b_m)/2`.
- `levelProduct_nbUnit`, `detProduct_mem_degLE`, `levelSpan_le_filtrationLevel`: on the lower
  unipotent group a level product is `∏_m gramWeight_m^{gramExp m}` times a polynomial of degree
  `≤ detDegree n h b`; with block polynomiality (`isBlockPoly_levelProduct`) this puts the level
  span in level `0` of `filtrationLevel` for the root `(r, i)`, the weights `gramWeight`, the
  exponents `gramExp` and the slope `c = (n + 1) + (n + 2) + 2n² + detDegree n h b`.

## Proof of the bound

The levels increase (`filtrationLevel_mono`) and right derivatives raise them by one
(`rightDerivative_mem_filtrationLevel`), so `U_d(𝔤) · E` lies in level `d`
(`finrank_filtrationSpan_le`). For a unisolvent set `S` of `bidegLT p q`
(`exists_finset_eval_injective`), level `d` has dimension `≤ |S| (c (d + 1) + 1)^{n(n-1)-2}`
(`finrank_filtrationLevel_le`), which is `≤ |S| (c + 1)^{n(n-1)-2} (d + 1)^{n(n-1)-1}`.

## Provenance

Internal infrastructure for the growth bound `ComplexLinkedSmallGrowthStatement`,
one of the two growth statements of the dimension-count route to
`ComplexLinkedLanglandsQuotientNotLargeStatement` in the Library module
`ComplexLinkedLanglandsQuotientGrowth`; see `ComplexLinkedSmallGrowthProof.md` for how the pieces
fit together. This route is an independent internal proof, not taken from the literature. The
module introduces no statement from the literature, and all its results are proved here.
