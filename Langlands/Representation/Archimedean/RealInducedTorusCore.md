# Torus averages along several induced blocks

Lean module: `Langlands.Representation.Archimedean.RealInducedTorusCore`.

This module is part of the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). For
pairwise disjoint blocks `p_1, …, p_r` the iterated mode-`0` coefficient
`coeffs (zeroModes slots) F 1 = ∫ F(r_{p_1}(θ_1) ⋯ r_{p_r}(θ_r)) dθ_1 ⋯ dθ_r` is the integral of
`F` over the torus of rotations of these blocks. The module computes such torus averages for
products `x ↦ u(x k) h(x g)` (Parseval), computes them exactly for block covariant functions with
tied exponents, and combines Parseval with the multi-block bound of `RealInducedBlockBound` into
a core bound. Unprefixed names below are in the namespace
`Langlands.Archimedean.RealInducedTorusCore`.

Notation follows `RealInducedBlockSlice.md` and `RealInducedBlockBound.md`. `GL_N(ℝ)` is
`Langlands.GeneralLinear N ℝ` and `O(N)` is the Library's `unitaryCompact ℝ N`. `r_p(θ)` is
`blockRotation N p θ`, and `Φ^p_j F (g) = ∫₀^{2π} F(r_p(θ) g) e^{−ijθ} dθ` is the Library's
`blockFourierCoefficient N p j F g`; `expMode j θ = e^{ijθ}` (Library `RealBlockFourierFinite`).
`b(x, y, w) = blockB h x y w`, `IsBlockCovariant`,
`Z(θ) = rotZ x y w θ = (e^y cos θ + w sin θ) + i e^x sin θ`,
`waveU x y w = ((e^x + e^y) − i w)/2` and `waveW x y w = ((e^y − e^x) + i w)/2` are from
`RealInducedBlockSlice`, and `Z(θ) = waveU · e^{iθ} + waveW · e^{−iθ}` there. `Slot`,
`Slot.Disjoint`, `coeffs`, `point`, `expBound`, `const`, `IsKFin` and `InClass` are from
`RealInducedBlockBound`. For a slot `s` the fields used are the block `s.p`, the mode `s.j` and
the coordinates `s.x, s.y, s.w`.

## Definitions

* `setMode s j`: the slot `s` with mode `j` (all other fields unchanged).
* `withModes slots J`: for `slots = [s_1, …, s_r]` and `J = [j_1, …, j_r]` the list
  `[setMode s_1 j_1, …, setMode s_r j_r]` (truncated to the shorter length).
* `zeroModes slots`: all slots with mode `0`.
* `modeLists D r`: the finite set of lists of length `r` with entries in `[−D, D]`.
* `HasDegree slots D u`: for every slot `s` of the list, every `j` with `D < |j|` and every
  `k ∈ O(N)`, `Φ^{s.p}_j u (k) = 0`.
* `invIntegral x y w = ∫₀^{2π} |Z(θ)|⁻¹ dθ`.
* `coreConst r D = ((2D + 1) · 2^{3D} (2D + 1) · 2π)^r`.

## Results

Modes.

* `sum_modeLists_succ`: `Σ_{J ∈ modeLists D (r+1)} f J = Σ_{j ∈ [−D, D]} Σ_{J ∈ modeLists D r} f (j :: J)`.
* `card_modeLists`: `modeLists D r` has `(2D + 1)^r` elements.
* `mem_modeLists`: a member of `modeLists D r` has length `r` and entries with `|j| ≤ D`.
* `mem_withModes`: every slot of `withModes slots J` is `setMode s j` for some slot `s` of
  `slots` and some `j`.
* `pairwise_withModes`, `pairwise_zeroModes`: changing modes preserves pairwise disjointness.
* `point_withModes`, `expBound_withModes`, `length_withModes`: if `J` has the length of `slots`,
  then `withModes slots J` has the same `point`, the same `expBound` and the same length as
  `slots`.
* `inClass_withModes`: `InClass slots D F` implies `InClass (withModes slots J) D F`.
* `const_withModes_le`: if `J` has the length of `slots` and entries with `|j| ≤ D`, then
  `const (withModes slots J) D ≤ (2^{3D} (2D + 1) · 2π)^{length slots}`.

Iterated coefficients.

* `coeffs_mul_right`: `coeffs L F (x g) = coeffs L (y ↦ F(y g)) (x)`.
* `coeffs_congr_of_eqOn`: if `F = F'` on `O(N)`, then `coeffs L F = coeffs L F'` on `O(N)`.
* `coeffs_eq_zero_of_eqOn`: if `F = 0` on `O(N)`, then `coeffs L F = 0` on `O(N)`.
* `norm_coeffs_le_of_mem`: if `|F| ≤ A` on `O(N)`, then `|coeffs L F (k)| ≤ (2π)^{length L} A`
  for `k ∈ O(N)`.
* `coeffs_mul_mem`: if `F` is right `O(N)`-invariant, then `coeffs L F (g k) = coeffs L F (g)` for
  `k ∈ O(N)`.

Parseval.

* `sum_Icc_eq_of_vanish`: for `D ≤ E`, if `f(j) = 0` whenever `D < |j|`, then the sums of `f`
  over `[−D, D]` and over `[−E, E]` agree.
* `eq_sum_of_degree`: let `p + 1 < N`, `u` continuous with `IsKFin u`, and
  `Φ^p_j u (k) = 0` for all `k ∈ O(N)` and `D < |j|`. Then for `k ∈ O(N)` and all `θ`:
  `u(r_p(θ) k) = (2π)⁻¹ Σ_{j ∈ [−D, D]} Φ^p_j u (k) e^{ijθ}`.
* `integral_mul_eq_sum` (**one block**): let `h` be continuous and suppose
  `u(r_p(θ) k) = (2π)⁻¹ Σ_{j ∈ [−D, D]} Φ^p_j u (k) e^{ijθ}` for all `θ`. Then for every `g`:

  `∫₀^{2π} u(r_p(θ) k) h(r_p(θ) g) dθ = (2π)⁻¹ Σ_{j ∈ [−D, D]} Φ^p_j u (k) · Φ^p_{−j} h (g)`.
* `coeffs_zeroModes_mul_eq_sum` (**several blocks**): let `slots` be pairwise disjoint of length
  `r`, `u` continuous with `IsKFin u` and `HasDegree slots D u`, and `h` continuous. Then for
  every `k ∈ O(N)` and every `g`:

  `coeffs (zeroModes slots) (x ↦ u(x k) h(x g)) 1 =
  (2π)^{−r} Σ_{J ∈ modeLists D r} coeffs (withModes slots J) u (k) ·
  coeffs (withModes slots (−J)) h (g)`,

  where `−J` is `J` with every entry negated.

Torus averages of tied functions.

* `continuous_inv_norm_rotZ`: `θ ↦ |Z(θ)|⁻¹` is continuous (`Z(θ) ≠ 0`).
* `norm_wave_le`: `|u e^{iθ} + w e^{−iθ}| ≤ |u| + |w|`.
* `norm_rotZ_lt`: `|Z(θ)| < 2 |waveU x y w|`.
* `pi_div_le_invIntegral`: `π / |waveU x y w| ≤ invIntegral x y w`.
* `invIntegral_pos`: `0 < invIntegral x y w`.
* `coeffs_zeroModes_point` (**exact torus average**): let `σ` assign a complex number to every
  slot, and let `E` be continuous and right `O(N)`-invariant. Let `slots` be pairwise disjoint and
  let `E` satisfy `IsBlockCovariant s.hp (σ s) (σ s − 1) E` for every slot `s`
  (`E(b_s(x, y, w) g) = e^{σ_s x + (σ_s − 1) y} E(g)`). Then

  `coeffs (zeroModes slots) E (point slots) =
  ∏_s e^{σ_s (x_s + y_s)} invIntegral(x_s, y_s, w_s) · E(1)`.

The core bound.

* `coreConst_nonneg`: `0 ≤ coreConst r D`.
* `norm_coeffs_zeroModes_le` (**core bound**): let `slots` be pairwise disjoint of length `r`,
  `u` continuous with `IsKFin u`, `HasDegree slots D u` and `|u| ≤ A` on `O(N)`, and let `h`
  satisfy `InClass slots D h` and `|h| ≤ B` on `O(N)`. Then for `k, k' ∈ O(N)`:

  `|coeffs (zeroModes slots) (x ↦ u(x k) h(x · point slots · k')) 1| ≤
  coreConst r D · A · B · expBound slots`.

## Proofs

* `modeLists`, `withModes` and the mode lemmas are inductions on the lists. `sum_modeLists_succ`
  uses that `(j, J) ↦ j :: J` is injective (`Finset.sum_image`, `Finset.sum_product`).
  `const_withModes_le` bounds each factor `2^{|j| + 2D}` by `2^{3D}`.
* `coeffs_mul_right`, `coeffs_congr_of_eqOn`, `coeffs_eq_zero_of_eqOn` and
  `norm_coeffs_le_of_mem` are inductions on `L`, using that `r_p(θ) k ∈ O(N)` for `k ∈ O(N)` and
  `RealInducedBlockBound.norm_blockFourierCoefficient_le`. `coeffs_mul_mem` is
  `coeffs_mul_right` plus invariance.
* `eq_sum_of_degree`: the Library's `exists_eq_sum_blockFourierCoefficient` gives an expansion
  over some `[−D', D']`; both `[−D, D]` and `[−D', D']` give the same sum as `[−max(D, D'), max(D, D')]`
  by `sum_Icc_eq_of_vanish`.
* `integral_mul_eq_sum`: substitute the expansion of `u`, exchange the finite sum and the
  integral (`intervalIntegral.integral_finsetSum`), and recognize
  `∫ h(r_p(θ) g) e^{ijθ} dθ = Φ^p_{−j} h (g)`.
* `coeffs_zeroModes_mul_eq_sum`: induction on `slots`. For `s :: rest`, the outer coefficient is
  `∫₀^{2π} coeffs (zeroModes rest) (x ↦ u(x k) h(x g)) (r_{s.p}(θ)) dθ`. By `coeffs_mul_right`
  and the induction hypothesis (at `r_{s.p}(θ) k ∈ O(N)` and `r_{s.p}(θ) g`) the integrand is
  `(2π)^{−(r−1)} Σ_J coeffs (withModes rest J) u (r_{s.p}(θ) k) ·
  coeffs (withModes rest (−J)) h (r_{s.p}(θ) g)`. For each `J` apply `integral_mul_eq_sum` at the
  block `s.p` to `coeffs (withModes rest J) u` and `coeffs (withModes rest (−J)) h`. The degree
  hypothesis for the first function holds because
  `Φ^{s.p}_j (coeffs (withModes rest J) u) = coeffs (withModes rest J) (Φ^{s.p}_j u)`
  (`RealInducedBlockBound.blockFourierCoefficient_coeffs`, disjointness) vanishes on `O(N)` for
  `D < |j|` by `coeffs_eq_zero_of_eqOn`. Finally `sum_modeLists_succ` reorders the double sum.
* `pi_div_le_invIntegral`: `|Z(θ)| ≤ |waveU| + |waveW| < 2|waveU|`
  (`RealInducedBlockSlice.norm_waveW_lt`), so `|Z(θ)|⁻¹ ≥ (2|waveU|)⁻¹` and the integral over
  `[0, 2π]` is at least `π/|waveU|`.
* `coeffs_zeroModes_point`: induction on `slots`. For `s :: rest` put
  `F = coeffs (zeroModes rest) E`; it is block covariant at `s` with exponents
  `(σ_s, σ_s − 1)` (`RealInducedBlockBound.isBlockCovariant_coeffs`) and right
  `O(N)`-invariant (`coeffs_mul_mem`). By `RealInducedBlockSlice.apply_blockRotation_mul_blockB`,
  `RealInducedBlockBound.blockRotation_mul_point` and right invariance,
  `F(r_{s.p}(θ) b_s · point rest) = e^{σ_s (x + y − log|Z(θ)|) + (σ_s − 1) log|Z(θ)|} F(point rest)
  = e^{σ_s (x + y)} |Z(θ)|⁻¹ F(point rest)`. Integrating over `θ` gives the factor
  `e^{σ_s (x_s + y_s)} invIntegral(x_s, y_s, w_s)`, and the induction hypothesis evaluates
  `F(point rest)`.
* `norm_coeffs_zeroModes_le`: by Parseval the average is
  `(2π)^{−r} Σ_{J ∈ modeLists D r} coeffs (withModes slots J) u (k) ·
  coeffs (withModes slots (−J)) h (point slots · k')`. For each `J`, the first factor is at most
  `(2π)^r A` (`norm_coeffs_le_of_mem`). For the second, `withModes slots (−J)` is pairwise
  disjoint, `h` is in its class (`inClass_withModes`), and it has the same `point` and `expBound`
  as `slots`; the multi-block bound `RealInducedBlockBound.norm_coeffs_point_mul_le` and
  `const_withModes_le` give at most `(2^{3D} (2D + 1) 2π)^r · B · expBound slots`. Summing over the
  `(2D + 1)^r` lists (`card_modeLists`) and multiplying by `(2π)^{−r}` gives the constant
  `coreConst r D`.

## Use

`coeffs_zeroModes_point` gives the exact torus average of a tied exponential function `E` at
`point slots`. Together with `pi_div_le_invIntegral`, its modulus is at least
`∏_s e^{Re σ_s (x_s + y_s)} π / |waveU_s| · |E(1)|`, which equals
`π^r · expBound slots · |E(1)|` when `Re σ_s = Re α_s − M_s/2` for every slot (`α_s = s.α`,
`M_s = s.M`). So the core bound compares the torus average of `u(· k) h(· point slots k')` with
the torus average of `E`. This lower bound and the resulting comparison are intended for the
torus-pairing bound in the proof of `RealStandardLanglandsQuotientStatement`; this module does not
state them.

## Provenance

This is derived, internal infrastructure for the proof of `RealStandardLanglandsQuotientStatement`;
it states no literature result. Parseval
along a block is the finite Fourier expansion of a right `O(N)`-finite function
(`exists_eq_sum_blockFourierCoefficient`), and the exact average is the Iwasawa decomposition
`r_p(θ) b(x, y, w) = b(x + y − log|Z|, log|Z|, ·) r_p(θ')` of `RealInducedBlockSlice`.
