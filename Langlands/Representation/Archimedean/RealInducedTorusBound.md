# The torus-pairing bound

Lean module: `Langlands.Representation.Archimedean.RealInducedTorusBound`.

This module is part of the proof
of `RealStandardLanglandsQuotientStatement` (module `RealLargeLanglandsQuotientReduction`). Let
`p_1, …, p_r` be pairwise disjoint blocks of `GL_N(ℝ)` and let `T` be the torus of their block
rotations. The module bounds the torus average `∫_T u(τ y_1) h(τ y_2) dτ` of a product of two
exponentially equivariant functions, uniformly in the two points `y_1, y_2`, by a constant times
the torus average of a product of two right `O(N)`-invariant comparison functions `E_u, E_h` with
real exponents. It states this bound as `RealInducedTorusBoundStatement` and proves it
(`realInducedTorusBound`). Unprefixed names below are in the namespace
`Langlands.Archimedean.RealInducedTorusBound`.

Notation follows `RealInducedBlockSlice.md`, `RealInducedBlockBound.md`,
`RealInducedBlockInvariance.md`, `RealInducedTorusCore.md` and `RealInducedTorusReduction.md`.
`GL_N(ℝ)` is `Langlands.GeneralLinear N ℝ`, `O(N)` is the Library's `unitaryCompact ℝ N`, and
smooth means `ContMDiff (matrixModel ℝ N) 𝓘(ℝ, ℂ) ∞`. For a slot `s` the fields used are the block
`s.p` with indices `ia s.hp = p` and `ib s.hp = p + 1`, the mode `s.j`, the coordinates
`s.x, s.y, s.w`, the exponent `s.α` and the weight `s.M`. From `RealInducedBlockBound`: `Slot`,
`Slot.Disjoint`, `coeffs`, `point`, `IsKFin`, `InClass` (`InClass slots D F`: `F` is continuous
and right `O(N)`-finite, and at every slot `s` it is block covariant with exponents
`(s.α, s.α − (s.M + 1))`, its block Fourier coefficients `Φ^{s.p}_j F` vanish identically unless
`j = ±(s.M + 1 + 2l)` with `l ∈ ℕ`, and vanish on `O(N)` for `|j| > D`), and
`expBound slots = ∏_s e^{(Re s.α − s.M/2)(s.x + s.y)} / |waveU s.x s.y s.w|`. From `RealInducedBlockInvariance`: `detFactor α slots =
∏_s exp((α_{s.p} − 1)(s.x + s.y))`. From `RealInducedTorusCore`: `setMode`, `zeroModes`,
`HasDegree`, `invIntegral`, `coreConst`. From `RealInducedTorusReduction`: `torus`, `IsAdapted`,
`chi α c = exp(Σ_i α_i log c_ii)`, `readSlots`. `RealBlockDerivative.IsExpEquivariant α φ`
(Library) means `φ(exp(diag x) · n · g) = e^{Σ_i α_i x_i} φ(g)` for all `x ∈ ℝ^N`, upper
unipotent `n` and `g`. For `slots` with all modes `0`, `coeffs slots F 1` is the iterated rotation
integral `∫ F(r_{p_1}(θ_1) ⋯ r_{p_r}(θ_r)) dθ_1 ⋯ dθ_r`, i.e. the integral over `T`.

## Statement

`RealInducedTorusBoundStatement`: for all `N, D`, every list `S` of pairwise disjoint slots,
`α_u, α_h : Fin N → ℂ`, `σ_u, σ_h : Fin N → ℝ` and functions `u, h, E_u, E_h : GL_N(ℝ) → ℂ` such
that

* `u` is smooth, `IsExpEquivariant α_u u`, `IsKFin u` and `HasDegree S D u`;
* `h` is smooth, `IsExpEquivariant α_h h` and `InClass S D h`;
* `E_u` is smooth, `IsExpEquivariant σ_u E_u`, `E_u(g k) = E_u(g)` for `k ∈ O(N)`, and `E_u(1) = 1`;
* `E_h` is smooth, `IsExpEquivariant σ_h E_h`, `E_h(g k) = E_h(g)` for `k ∈ O(N)`, and `E_h(1) = 1`;
* at every slot `s ∈ S`, with `p = s.p`:
  `(α_u + α_h)_p − (α_u + α_h)_{p+1} = 2`, `(σ_u + σ_h)_p − (σ_u + σ_h)_{p+1} = 2`,
  `Re (α_u + α_h)_p = (σ_u + σ_h)_p`, `σ_{h,p+1} = σ_{h,p} − 1` and
  `σ_{h,p} = Re s.α − s.M/2`;
* at every index `i` that is not `p` or `p + 1` for a slot of `S`:
  `Re α_{u,i} = σ_{u,i}` and `Re α_{h,i} = σ_{h,i}`;

there is a real `C` such that for all `y_1, y_2 ∈ GL_N(ℝ)`

`‖coeffs (zeroModes S) (x ↦ u(x y_1) h(x y_2)) 1‖ ≤
C · ‖coeffs (zeroModes S) (x ↦ E_u(x y_1) E_h(x y_2)) 1‖`.

The constant is `coreConst r D · A · B / π^r`, where `r` is the length of `S` and `A`, `B` bound
`|u|`, `|h|` on `O(N)`.

## Results

Equivariance.

* `isExpEquivariant_mul_right`: if `IsExpEquivariant α φ`, then `IsExpEquivariant α (x ↦ φ(x g))`.
* `isExpEquivariant_mul`: if `IsExpEquivariant α φ` and `IsExpEquivariant β ψ`, then
  `IsExpEquivariant (α + β) (x ↦ φ(x) ψ(x))`.

Slots read off from a matrix.

* `mem_readSlots_zeroModes`: every slot of `readSlots C (zeroModes S)` is `readSlot C (setMode s 0)`
  for some `s ∈ S`.
* `setMode_mem_zeroModes`: `s ∈ S` implies `setMode s 0 ∈ zeroModes S`.
* `coeffs_readSlots_zeroModes`: `coeffs (zeroModes (readSlots C (zeroModes S))) F =
  coeffs (zeroModes S) F`.
* `length_readSlots_zeroModes`: `readSlots C (zeroModes S)` has the length of `S`.
* `inClass_readSlots_zeroModes`, `hasDegree_readSlots_zeroModes`: `InClass S D F` and
  `HasDegree S D F` pass to `readSlots C (zeroModes S)` (the block, exponent and weight of every
  slot are unchanged).

Norms of the scalar factors.

* `norm_chi_eq`: if `IsAdapted L c` and `Re α_i = σ_i` at every index `i` outside the blocks of
  `L`, then `‖chi α c‖ = ‖chi σ c‖`.
* `norm_detFactor_eq`: if `Re α_{s.p} = σ_{s.p}` for every slot `s` of `L`, then
  `‖detFactor α L‖ = ‖detFactor σ L‖`.
* `expBound_cons`, `expBound_nonneg`: the recursion for `expBound` and `0 ≤ expBound L`.
* `pi_pow_mul_expBound_le`: if `σ_s = Re s.α − s.M/2` for every slot `s` of `L`, then
  `π^{|L|} · expBound L ≤ ‖∏_{s ∈ L} e^{σ_s (s.x + s.y)} invIntegral(s.x, s.y, s.w)‖`.

The reduction.

* `coeffs_reduce` (**reduction of a torus pairing**): let `S` be pairwise disjoint, `φ, ψ` smooth
  with `IsExpEquivariant a φ`, `IsExpEquivariant b ψ`, and
  `(a + b)_{s.p} − (a + b)_{s.p+1} = 2` for `s ∈ S`. Write `Z = zeroModes S`,
  `Y_i = point (readSlots C_i Z)`, and let `c_1, c_3` be adapted to `Z` with
  `Y_1⁻¹ y_2 = c_3 · (Y_3 · k_3)`. Then
  `coeffs Z (x ↦ φ(x c_1 Y_1 k_1) ψ(x y_2)) 1 =
  chi a c_1 · detFactor (a + b) (readSlots C_1 Z) · chi b c_3 ·
  coeffs Z (x ↦ φ(x k_1) ψ(x Y_3 k_3)) 1`.
* `norm_coeffs_le_mul_norm_coeffs` (**torus-pairing bound**): the statement above.
* `realInducedTorusBound`: `RealInducedTorusBoundStatement` holds.

## Proofs

* `isExpEquivariant_mul_right`: `exp(diag x) n g' g = exp(diag x) n (g' g)`.
  `isExpEquivariant_mul`: multiply the two equivariance identities; `e^{a}e^{b} = e^{a+b}`.
* `coeffs_readSlots_zeroModes` is `coeffs_congr_map` (the lists have the same blocks and modes);
  the transfer lemmas use `mem_readSlots_zeroModes` and that `readSlot` and `setMode` change only
  the coordinates and the mode of a slot, on which the per-slot conditions of `InClass` and
  `HasDegree` do not depend.
* `norm_chi_eq`: by `norm_chi`, `‖chi α c‖ = exp(Σ_i Re α_i log c_ii)`. At an index outside the
  blocks the exponents agree; at an index of a block of `L` the adapted `c` has `c_ii = 1`, so
  the term vanishes for both sides.
* `norm_detFactor_eq`: induction on `L`, `‖exp z‖ = exp(Re z)`.
* `pi_pow_mul_expBound_le`: induction on `L`, using `pi_div_le_invIntegral`
  (`π/|waveU| ≤ invIntegral`) and `invIntegral_pos`.
* `coeffs_reduce`: by `coeffs_mul_adapted` (with `IsExpEquivariant a φ` and `c_1` adapted) the
  left side is `chi a c_1 · coeffs Z (x ↦ φ(x Y_1 k_1) ψ(x y_2)) 1`. With
  `G(x) = φ(x k_1) ψ(x Y_1⁻¹ y_2)` the integrand is `x ↦ G(x Y_1)`; `G` is smooth and
  `IsExpEquivariant (a + b) G` (the two lemmas above). By `coeffs_mul_right` the average is
  `coeffs Z G Y_1`. The slots `readSlots C_1 Z` are pairwise disjoint (`pairwise_readSlots`), have
  mode `0`, and satisfy the gap-2 condition for `a + b`, so `coeffs_point_mul`
  (`RealInducedBlockInvariance`) together with `coeffs_readSlots` gives
  `coeffs Z G (Y_1 · 1) = detFactor (a + b) (readSlots C_1 Z) · coeffs Z G 1`. Finally
  `G(x) = φ(x k_1) ψ(x c_3 Y_3 k_3)`, and `coeffs_mul_adapted'` (with `IsExpEquivariant b ψ`)
  removes `c_3` at the cost of `chi b c_3`.
* `norm_coeffs_le_mul_norm_coeffs`: `O(N)` is compact
  (`RealPrincipalSeriesDuality.compactSpace_unitaryCompact`), so `|u| ≤ A` and `|h| ≤ B` on
  `O(N)`. Fix `y_1, y_2`. `exists_decomp` writes `y_1 = c_1 (Y_1 k_1)` and
  `Y_1⁻¹ y_2 = c_3 (Y_3 k_3)` with `c_1, c_3` adapted to `Z = zeroModes S` and `k_1, k_3 ∈ O(N)`.
  Apply `coeffs_reduce` to both sides: to `(u, h)` with exponents `(α_u, α_h)` and to
  `(E_u, E_h)` with exponents `(σ_u, σ_h)`; the gap-2 hypotheses are exactly those of the
  statement. By `norm_chi_eq` and `norm_detFactor_eq` (with the hypotheses on real parts) the
  three scalar factors of the two sides have the same norm `X ≥ 0`. It remains to compare the
  reduced averages.
  * Upper bound: `norm_coeffs_zeroModes_le` (`RealInducedTorusCore`), applied to the slots
    `Z_3 = readSlots C_3 Z` (pairwise disjoint, with `HasDegree` and `InClass` transferred), gives
    `‖coeffs Z (x ↦ u(x k_1) h(x Y_3 k_3)) 1‖ ≤ coreConst r D · A · B · expBound Z_3`.
  * Exact value: on the torus (`torus_le_unitaryCompact`), `E_u(x k_1) = E_u(1) = 1` and
    `E_h(x Y_3 k_3) = E_h(x Y_3)` by right `O(N)`-invariance, so by `coeffs_congr_torus` and
    `coeffs_mul_right` the comparison average is `coeffs Z E_h Y_3`. `E_h` is block covariant
    with tied exponents `(σ_{h,p}, σ_{h,p} − 1)` at every block (`isBlockCovariant_of_isExpEquivariant`
    and `σ_{h,p+1} = σ_{h,p} − 1`), so `coeffs_zeroModes_point` (`RealInducedTorusCore`) gives
    `coeffs Z E_h Y_3 = ∏_{s ∈ Z_3} e^{σ_{h,s.p}(s.x + s.y)} invIntegral(s.x, s.y, s.w)`.
  * Lower bound: since `σ_{h,p} = Re s.α − s.M/2`, `pi_pow_mul_expBound_le` gives
    `π^r · expBound Z_3 ≤ ‖coeffs Z (x ↦ E_u(x k_1) E_h(x Y_3 k_3)) 1‖`.

  Hence `X · ‖reduced u-h average‖ ≤ X · coreConst r D · A · B · expBound Z_3 ≤
  (coreConst r D · A · B / π^r) · X · ‖reduced E-average‖`.

## Use

In the proof of `RealStandardLanglandsQuotientStatement` for standard modules with discrete-series blocks, `u` and `h` are
K-finite vectors of the two induced representations being paired, and `E_u, E_h` are the
spherical comparison functions with real exponents (`E_h` tied at the blocks). The bound
dominates the torus-averaged pairing of `u` and `h` by that of the comparison functions, whose
integrability over the remaining coordinates is controlled separately.

## Provenance

This is derived, internal infrastructure for the proof of `RealStandardLanglandsQuotientStatement`; it states no literature result. It
combines the multi-block bound (`RealInducedBlockBound`, from a contour shift in the `GL_2`
integrals of the discrete-series `K`-types), the mode-`0` invariance (`RealInducedBlockInvariance`,
from the Library's tridiagonal derivative formula), the Parseval core bound and exact torus
average (`RealInducedTorusCore`), and the reduction to block coordinates
(`RealInducedTorusReduction`, from the Iwasawa decomposition).
