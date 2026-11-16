# Fourier coefficients along several disjoint induced blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedBlockBound`.

Worker 5220 wrote this module for Task 6749 (`5dd3db87-6f14-4d0f-b9a7-3d0065415fd8`), the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). It
extends the one-block bound of `RealInducedBlockSlice` to a list of pairwise disjoint induced
(discrete-series) blocks `D_{m_1}, …, D_{m_r}`. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealInducedBlockBound`.

Notation follows `RealInducedBlockSlice.md`. `GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ` and
`O(N)` is the Library's `unitaryCompact ℝ N`. `r_p(θ)` is `blockRotation N p θ`, and
`Φ^p_j F (g) = ∫₀^{2π} F(r_p(θ) g) e^{−ijθ} dθ` is the Library's
`blockFourierCoefficient N p j F g`. `b(x, y, w) = blockB h x y w` is the matrix that is
`[[e^x, w], [0, e^y]]` on the block `p, p + 1` and the identity elsewhere.
`IsBlockCovariant`, `blockMat` and `waveU x y w = ((e^x + e^y) − i w)/2` are from
`RealInducedBlockSlice`.

## Definitions

* `blockDelta h a b c d`: the `N × N` real matrix that is `[[a, b], [c, d]]` on the block
  `p, p + 1` and `0` elsewhere.
* `IsKFin F`: `F` is right `O(N)`-finite, i.e. `F` lies in the Library's
  `kFiniteVectors (Whittaker.rightTranslation ℂ (GL_N(ℝ))) (unitaryCompact ℝ N)`.
* `Slot N`: a block together with evaluation data. Its fields are the block start `p` with
  `hp : p + 1 < N`, a covariance exponent `α ∈ ℂ`, a weight `M ∈ ℕ`, a Fourier mode `j ∈ ℤ`, and
  real numbers `x, y, w` (the coordinates of `b(x, y, w)` on the block).
* `Slot.Disjoint s t`: `s.p + 1 < t.p` or `t.p + 1 < s.p`.
* For a list `slots = [s_1, …, s_r]`:
  * `coeffs slots F = Φ^{p_1}_{j_1} (Φ^{p_2}_{j_2} ( ⋯ Φ^{p_r}_{j_r} F))` (`coeffs [] F = F`);
  * `point slots = b_1(x_1, y_1, w_1) ⋯ b_r(x_r, y_r, w_r)` (`point [] = 1`);
  * `expBound slots = ∏_i e^{(Re α_i − M_i/2)(x_i + y_i)} / |u_i|`, `u_i = waveU x_i y_i w_i`;
  * `const slots D = ∏_i 2^{|j_i| + 2D} (2D + 1) · 2π`.
* `IsMode M j`: there is `l ∈ ℕ` with `j = M + 1 + 2l` or `j = −(M + 1 + 2l)`.
* `SlotCond s D F`: (i) `IsBlockCovariant s.hp α (α − (M + 1)) F` (with `α = s.α`, `M = s.M`);
  (ii) `Φ^{s.p}_j F (g) = 0` for all `g` and all `j` with `¬ IsMode M j`; (iii)
  `Φ^{s.p}_j F (k) = 0` for all `k ∈ O(N)` and all `j` with `D < |j|`.
* `InClass slots D F`: `F` is continuous, `IsKFin F`, and `SlotCond s D F` for every `s` in the
  list.

## Results

Disjoint blocks.

* `blockMat_eq_one_add`: `blockMat h a b c d = 1 + blockDelta h (a − 1) b c (d − 1)`.
* `blockDelta_mul_blockDelta`: for disjoint blocks `p, p'` the product of `blockDelta` matrices
  is `0`.
* `blockMat_commute`: block matrices on disjoint blocks commute.
* `blockRotation_mul_blockB_comm`: for disjoint blocks,
  `r_p(θ) · b_{p'}(x, y, w) = b_{p'}(x, y, w) · r_p(θ)`.
* `blockRotation_mul_point`: `r_p(θ)` commutes with `point rest` if the block `p` is disjoint
  from every block of `rest`.

Fourier coefficients.

* `blockFourierCoefficient_eq_zero_of`: if `F(r_p(θ) g) = 0` for all `θ`, then `Φ^p_j F (g) = 0`.
* `norm_blockFourierCoefficient_le`: if `|F(r_p(θ) g)| ≤ B` for all `θ`, then
  `|Φ^p_j F (g)| ≤ 2πB`.
* `isKFin_blockFourierCoefficient`: for continuous `F` with `IsKFin F`, every `Φ^p_j F` is right
  `O(N)`-finite.
* `isKFin_leftTranslate`: if `IsKFin F`, then `y ↦ F(Y y)` is right `O(N)`-finite for every
  `Y ∈ GL_N(ℝ)`.
* `isBlockCovariant_blockFourierCoefficient`: block covariance at a block `p` is preserved by
  `Φ^{p'}_j` for a disjoint block `p'`.
* `continuous_coeffs`, `isKFin_coeffs`: iterated coefficients of a continuous `O(N)`-finite
  function are continuous and `O(N)`-finite.
* `blockFourierCoefficient_coeffs`: `Φ^p_j (coeffs rest F) = coeffs rest (Φ^p_j F)` for
  continuous `F` if `p` is disjoint from all blocks of `rest`.
* `isBlockCovariant_coeffs`: block covariance at `p` passes to `coeffs rest F` under the same
  disjointness.
* `slotCond_blockFourierCoefficient`: if `s` and `t` are disjoint and `F` is continuous with
  `SlotCond t D F`, then `SlotCond t D (Φ^{s.p}_j F)` for every `j`.
* `card_filter_abs_le`: `#{j ∈ [−D', D'] : |j| ≤ D} ≤ 2D + 1`.

The bound.

* `norm_coeffs_point_mul_le` (**multi-block bound**). Let `D ∈ ℕ`, let `slots` be a list of
  pairwise disjoint slots (`slots.Pairwise Slot.Disjoint`), and let `F` satisfy
  `InClass slots D F` and `|F(k)| ≤ B` for all `k ∈ O(N)`. Then for every `k ∈ O(N)`:

  `|coeffs slots F (point slots · k)| ≤ const slots D · B · expBound slots`.

  The constant depends only on the modes `j_i`, the number of slots and `D`, not on `F`.

## Statement

`Langlands.Archimedean.RealInducedBlockBoundStatement` (outside the namespace above) is the
proposition form of `norm_coeffs_point_mul_le`: for all `N`, `D`, pairwise disjoint `slots`,
`F` with `InClass slots D F` and `B` with `|F(k)| ≤ B` on `O(N)`, and all `k ∈ O(N)`,
`|coeffs slots F (point slots · k)| ≤ const slots D · B · expBound slots`.
`Langlands.Archimedean.realInducedBlockBound` proves it by `norm_coeffs_point_mul_le`.

## Proofs

`blockMat_commute`: write each block matrix as `1 + Δ` with `Δ = blockDelta`. Products
`Δ_p Δ_{p'}` of disjointly supported matrices vanish entrywise (`split_ifs` and `omega` on the
indices), so `(1 + Δ)(1 + Δ') = 1 + Δ + Δ' = (1 + Δ')(1 + Δ)`.
`blockRotation_mul_blockB_comm` applies this to `RealInducedBlockSlice.blockRotation_eq_blockMat`
and `blockB_eq_blockMat`. `blockRotation_mul_point` is an induction on the list.

`norm_blockFourierCoefficient_le` is Mathlib's `intervalIntegral.norm_integral_le_of_norm_le_const`,
since `|e^{−ijθ}| = 1`. `isKFin_blockFourierCoefficient`: every function in the span
`V` of the right `O(N)`-translates of `F` is continuous (`Submodule.span_induction`). So `Φ^p_j`
is a linear map `L` on `V` (Library `RealBlockJacquet.blockFourierCoefficient_add` and
`blockFourierCoefficient_smul`, which need continuity). Its range is finite-dimensional. The Library
`blockFourierCoefficient_rightTranslation` shows that the right `O(N)`-translates of `Φ^p_j F` lie
in that range. `isKFin_leftTranslate`: left translation by `Y` is linear and maps the translates
of `F` to those of `y ↦ F(Y y)`, so the span of the latter lies in the image of `V`.
`isBlockCovariant_blockFourierCoefficient` moves `b(x, y, w)` past `r_{p'}(θ)` inside the
integral by `blockRotation_mul_blockB_comm`. `blockFourierCoefficient_coeffs` is an induction on
`rest` using the Library `RealBlockFourierFinite.blockFourierCoefficient_comm` (coefficients along
disjoint blocks of a continuous function commute) together with the continuity of iterated
coefficients. `slotCond_blockFourierCoefficient`: covariance is
`isBlockCovariant_blockFourierCoefficient`. For (ii) and (iii), commute `Φ^{t.p}_{j'}` past
`Φ^{s.p}_j`; for (iii) also use that `r_{s.p}(θ) k ∈ O(N)` (`blockRotation_mem_unitaryCompact`).

`norm_coeffs_point_mul_le` is proved by induction on the list, for all `F` and `B` at once. The
empty list is the hypothesis `|F(k)| ≤ B`. For `s :: rest`, put `G = coeffs rest F`,
`Y = point rest` and `F_j = Φ^{s.p}_j F`.

1. Each `F_j` satisfies `InClass rest D F_j` (continuity, `isKFin_blockFourierCoefficient`,
   `slotCond_blockFourierCoefficient`).
2. Expansion at the point. The left translate `y ↦ G(Y y)` is continuous and right
   `O(N)`-finite (`isKFin_coeffs`, `isKFin_leftTranslate`). The Library
   `RealBlockFourierFinite.exists_eq_sum_blockFourierCoefficient` gives `D'` with
   `G(Y r_p(φ) k) = (2π)⁻¹ Σ_{|j| ≤ D'} Φ^p_j(G(Y ·))(k) e^{ijφ}`. Since `r_p(φ)` commutes with
   `Y` (`blockRotation_mul_point`) this is the expansion of `φ ↦ G(r_p(φ) Y k)`. Its coefficients
   are `c_j = Φ^p_j G (Y k) = coeffs rest F_j (Y k)` (`blockFourierCoefficient_coeffs`).
3. Vanishing coefficients. If `¬ IsMode s.M j` or `D < |j|`, then `F_j = 0` on `O(N)` by
   `SlotCond s D F`. The induction hypothesis for `F_j` with `B = 0` gives `c_j = 0`. So the sum
   can be restricted to `S = {j ∈ [−D', D'] : |j| ≤ D}` (`Finset.sum_filter_of_ne`), and every
   `j ∈ S` with `c_j ≠ 0` satisfies `IsMode s.M j`.
4. Size of the coefficients. `|F_j| ≤ 2πB` on `O(N)` (`norm_blockFourierCoefficient_le`, since
   `r_p(θ) k ∈ O(N)`). The induction hypothesis gives
   `|c_j| ≤ const rest D · 2πB · expBound rest`, and with `card_filter_abs_le`,
   `Σ_{j ∈ S} |c_j| ≤ (2D + 1) · const rest D · 2πB · expBound rest`.
5. One block. `G` is block covariant at `s` (`isBlockCovariant_coeffs`). The one-block bound
   `RealInducedBlockSlice.norm_blockFourierCoefficient_blockB_le` at the point `g = Y k`, with
   the expansion of step 2 on `S`, gives
   `|Φ^{s.p}_{s.j} G (b_s · Y k)| ≤ 2^{|j_s| + 2D} (Σ_{j ∈ S} |c_j|) e^{(Re α_s − M_s/2)(x_s + y_s)} / |u_s|`.
   Since `point (s :: rest) · k = b_s · (Y k)`, steps 4 and 5 multiply out to the claim.

## Use

For a function in a real standard module whose list contains the induced blocks `s_1, …, s_r`,
`InClass` holds by `RealInducedBlockSlice.isBlockCovariant_of_isExpEquivariant` and the module's
Fourier conditions (see `RealInducedBlockSlice.md`, section Use). The bound controls the
torus Fourier coefficients of such a function at an Iwasawa point by the tied exponentials of the
induced blocks, uniformly in `sup_{O(N)} |F|`.

## Provenance

This is derived, internal infrastructure for Task 6749; it states no literature result. The
induction over blocks, with the left-translate expansion at a point outside `O(N)` and the
`B = 0` argument for vanishing coefficients, is this module's own.
