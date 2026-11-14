# The extensions by zero generate the principal series

Author: Worker 392.

This helper module of the proof of
`Langlands.Conductor.OrderedUnramifiedSphericalCyclicityStatement` (see
[`OrderedUnramifiedSphericalCyclicity`](../OrderedUnramifiedSphericalCyclicity.md))
proves **Step C**. Let `S` be a subrepresentation of the principal series of rank
`n + 2` with parameters `z` that contains `extend ψ` for every `ψ` in the principal
series of rank `n + 1` with parameters `tailParam z` (see
[`Extension`](Extension.md)). Then `S = ⊤`. The definitions are internal auxiliary
constructions, with no literature source. All declarations are in
`Langlands.Conductor.SphericalCyclicity`. Write `K = integralSubgroup 𝒪 m`, `K_a` for
the Library's `principalLevelSubgroup F m a`, and `B` for `Borel m`.

## The sets `B K_a` and a finite cover of `K`

- `conj_mem_principalLevel`: `K` normalizes `K_a`. The proof follows the pattern of
  the corresponding Library argument: `K_a` is the image of the kernel of reduction
  modulo `𝔪^a`, and conjugating by an element of `K` preserves that kernel.
- `InBK m a x` means `x = b k` with `b ∈ B` and `k ∈ K_a`. It is stable under left
  multiplication by `B` (`inBK_borel_mul_iff`) and under right multiplication by
  `K_a` (`inBK_mul_iff`). `inBK_translate_iff` gives
  `InBK (x k κ⁻¹) ↔ InBK (x κ⁻¹)` for `κ ∈ K` and `k ∈ K_a`, by normality.
- `exists_cover`: there is a finite `T ⊆ K` such that every `k ∈ K` satisfies
  `k κ⁻¹ ∈ K_a` for some `κ ∈ T`. The proof uses compactness of `K`
  (`isCompact_principalLevelOpenSubgroup F m 0` and `principalLevelSubgroup_zero`),
  covered by the open sets `K_a κ`.

## Cutting off principal-series functions

- `ext_value`, `value_sub` and `value_zero`: functions are equal when their values
  agree, and evaluation is additive.
- `cut U hB hU f hf` is `x ↦ [U x] f x`, for a predicate `U` that is left
  `B`-invariant and right `K_a`-invariant and a function `f` fixed by `K_a`. It lies
  in the principal series: covariance comes from `hB`, and smoothness comes from the
  open subgroup `K_a` (`hU`, `hf`). `value_cut` evaluates it. `cut_mul` says that it
  is again fixed by `K_a`.
- `translate_right_inv`: for `κ ∈ K`, the translate `ρ(κ) f` is fixed by `K_a` when
  `f` is, by normality.

## Cellular functions

- `lowerUnip_mul_blockDiag_one`: `L(y) diag(α, 1) = diag(α, 1) L(α y)`.
  `blockDiag_one_mul_comm`: `diag(1, h)` and `diag(α, 1)` commute.
  `lowGL_blockDiag`: `lowGL diag(α, h) = h`.
- `lowerUnip_mem_principalLevel`: `L(y) ∈ K_a` if every `v (y i) ≤ (v ϖ)^a`.
  `blockDiag_one_mem_principalLevel`: `diag(1, h) ∈ K_a` for `h` in level `a` of
  `GL_(n+1)`.
- `val_cellVec_le`: for `k ∈ K_a` with `a > 0`, every coordinate of `cellVec k` has
  valuation at most `(v ϖ)^a`.
- `tHead ϖ a = diag(ϖ^(a-1), 1, …, 1)`. `inCell_mul_tHead_inv`: for `a > 0` and
  `k ∈ K_a`, the element `k tHead⁻¹` lies in the cell. `inCell_of_inBK`: if
  `InBK (x tHead)`, then `InCell x`.
- `lowerUnip_smul_mem`: if `y` is small, then `L(ϖ^(a-1) y) ∈ K_a`.
- `isUpperTriangular_of_colT_low`: a matrix with `colT = 0` and `low = 1` is upper
  triangular.
- `cell_decomp`: every `x` in the cell is `b diag(1, D) L(y)` with `b ∈ B` and `y`
  small. Take `y = cellVec x`, `p = x L(-y)`, `D = lowGL p` and
  `b = p diag(1, D)⁻¹`.
- `eq_of_inCell`: two functions that are covariant for the same `χ` on `B`, right
  invariant under the small lower unipotents, and equal on all `diag(1, D)` agree on
  the cell.

## Restriction to the block-diagonal matrices

For `G` in the principal series of rank `n + 2`:

- `borelHead b = diag(1, b)`, with `borelHead_val`, `lowBorel_borelHead` and
  `diagonalUnit_borelHead`. `normalizedCharacter_borelHead`:
  `χ_z(diag(1, b)) = s^(ordDet b) χ_(tailParam z)(b)`, from
  `normalizedCharacter_split`.
- `restrictFun G D = s^(-ordDet D) G(diag(1, D))`. It is covariant for
  `χ_(tailParam z)` (`restrictFun_borel_mul`). It is fixed by level `a` when `G` is
  fixed by the matrices `diag(1, h)` of level `a` (`restrictFun_mul_level`).
- `restrict G hG` is the resulting element of the principal series of rank `n + 1`,
  and `value_restrict` evaluates it.
- `isSmall_add_iff` and `extFun_mul_lowerUnip_small`: an extension by zero is right
  invariant under the small lower unipotents. `cellScalar_blockDiag_one` and
  `extFun_blockDiag_one`: `extFun ψ (diag(1, D)) = s^(ordDet D) ψ(D)`.
- `extend_restrict`: suppose `G` vanishes off the cell, is right invariant under
  the small lower unipotents, and is fixed by the matrices `diag(1, h)` of level `a`.
  Then `extend (restrict G) = G`. On the cell this follows from `eq_of_inCell`. Off
  the cell both sides vanish.

## Step C

- `mem_of_support_inBK`: let `a > 0`, and let `g` be fixed by `K_a` and vanish off
  `B K_a`. Then `g ∈ S`. Proof: put `G = ρ(tHead) g`. Then `G` vanishes off the cell
  (`inCell_of_inBK`). It is right invariant under `L(y)` for small `y`. Indeed
  `lowerUnip_mul_blockDiag_one` gives `L(y) tHead = tHead L(ϖ^(a-1) y)`, that is,
  `tHead⁻¹ L(y) tHead = L(ϖ^(a-1) y)`, and `L(ϖ^(a-1) y) ∈ K_a` by
  `lowerUnip_smul_mem`. Hence
  `G(x L(y)) = g(x L(y) tHead) = g(x tHead L(ϖ^(a-1) y)) = g(x tHead) = G(x)`.
  It is also right invariant under `diag(1, h)` of level `a`, because `diag(1, h)`
  commutes with `tHead` (`blockDiag_one_mul_comm`) and lies in `K_a`. So
  `G = extend (restrict G) ∈ S`, and `g = ρ(tHead⁻¹) G ∈ S`.
- `cut_translate_mem`: for `κ ∈ K`, the piece `[x κ⁻¹ ∈ B K_a] g(x)` of `g` lies in
  `S`. It equals `ρ(κ⁻¹)` applied to the piece of `ρ(κ) g` supported on `B K_a`,
  which lies in `S` by the previous item.
- `eq_top_of_extend_mem`: let `f` be arbitrary, fixed by `K_a` with `a = level f`,
  and take a finite cover `T` from `exists_cover`. Induction over finite subsets
  `T' ⊆ T` shows the following. Every `g` fixed by `K_a` that vanishes at every `x`
  with `x κ⁻¹ ∉ B K_a` for all `κ ∈ T'` lies in `S`. The inductive step writes `g` as
  its piece for the new `κ` plus a remainder. By the Iwasawa decomposition
  (`exists_borel_integral`) and the cover, `f` satisfies the hypothesis for `T`.
  Hence `f ∈ S`.
