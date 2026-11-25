# Interlaced induction blocks: the engine of the chain

Lean module: `Langlands.Representation.Archimedean.RealInterlacedEngine`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`.

Fourth of the six modules that prove `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`
(see `RealInterlacedMirror.md`). It imports `RealInterlacedChain`. It contains the main evaluation
`main_value`, which is shared by the two cases `A ≥ C` (`RealInterlacedProof`) and `C > A`
(`RealInterlacedMirror`), and the test functions and test vectors. The notation is that of
`RealInterlacedJacquet.md`, `RealInterlacedColumns.md` and `RealInterlacedChain.md`. `Ψ = frobMap`
denotes Frobenius maps (module `RealCharacterCrossing`).

## Generic lemmas (section Generic)

* `finsum_sign_two`: if `c_j = 0` for `j ≠ ±N` with `N > 0`, then `Σᶠ_j sgn(j) c_j = c_N - c_{-N}`.
* `frobMap_eq_two_mode` (**a flat step on two modes**): if
  `w(r_b(φ) κ) = e^{iNφ} A(κ) + e^{-iNφ} B(κ)` for every `κ ∈ SO(n)` and `N ≠ 0`, then on `SO(n)`
  the Frobenius map of `ℓ_μ` at `b` takes the value `(Ψ w)(κ) = μ_N A(κ) + μ_{-N} B(κ)`. This is
  `frobFun_apply_of_mem` (Library) with `finsum_blockFourier_two_mode` (`RealBlockFlatJacquet`).
* `continuous_binom`, `coeff_binom_pair`: the coefficient at `σ j` of
  `c₁ (a₁ e^{iσt} + b₁)^N + c₂ (a₂ e^{iσt} + b₂)^N` is
  `2π C(N, j) (c₁ a₁^j b₁^{N-j} + c₂ a₂^j b₂^{N-j})` (`coeff_binom`).

## The main evaluation (section Main)

`main_value` is stated for `GL₄`, a list `ds0`, vectors `u, u'` and `r, m` with `r + m > 0`. Let
`S = Sm u u' r m = L_y^r L_w^m` and `T = yZ h41 u ^ r · w₊ ^ m`. The hypotheses are:

* `w₀ ∈ KF 4 ds0` agrees on `SO(4)` with some `H₁ ∈ S`;
* `ℓ₁ = ℓ_{μ₁}` at the middle block `1` is a real Jacquet functional on `ds0` (exponents `a₁`,
  signs `e₁`), and `ℓ₂ = ℓ_{μ₂}` at an outer block `b₂` is a real Jacquet functional on
  `PL (expo a₁) e₁` with `μ₂` nowhere zero, and `S` has expansions along `b₂`;
* let `w = Ψ₂ Ψ₁ w₀`. Its window `|j| + 1 < r + m` at the block `1` vanishes on `O(4)`, and
  `r + m ≡ par h41 e₂ (mod 2)`;
* for some `κ₀ ∈ SO(4)` and `j*` with `μ₁(j*) ≠ 0`, the coefficient at `j*` of
  `t ↦ H₁(r₁(t) κ₀)` is nonzero (`hval`);
* `hfin`: for every `g ≠ 0`, the coefficient at `j_f` of
  `θ ↦ 2π g (T(r_{rb}(θ)) - (-1)^{e₂(2) + e₂(3)} T(s₃ s₂ r_{rb}(θ)))` is nonzero.

The conclusion is that the coefficient at `j_f` of `θ ↦ Σᶠ_j sgn(j) Φ^{(1)}_j(w)(r_{rb}(θ))` is
nonzero. This is the hypothesis `hmain` of the dichotomy `exists_of_dichotomy`
(`RealInterlacedJacquet`) for the intertwiner `Ψ₂ Ψ₁`.

Proof.

1. Two steps of `frobMap_eq_on` (using `hasExpTop_Sm1` along `1` and the hypothesis along `b₂`)
   give `H₃ ∈ S` with `w = H₃` on `SO(4)`. By `hasExpTop_Sm1` the top coefficient of `H₃` along
   the middle block is `g T` for some `g ∈ ℂ`.
2. For `κ ∈ SO(4)`: `Φ^{(1)}_{r+m}(w)(κ) = 2π g T(κ)`
   (`blockFourierCoefficient_eq_of_expansion`). Then
   `Φ^{(1)}_{-(r+m)}(w)(κ) = (-1)^{e₂(2) + e₂(3)} 2π g T(s₃ s₂ κ)`
   (`blockFourierCoefficient_neg_one`). All other modes vanish
   (`blockFourierCoefficient_one_eq_zero`).
3. `g ≠ 0`. Otherwise all modes of `w` vanish on `SO(4)`, so `w = 0` there (`eq_zero_of_modes`).
   Going back through `Ψ₂` (`blockFourierCoefficient_eq_zero_of_frobMap`, `μ₂` has no zeros) and
   `eq_zero_of_modes` along `b₂`, `Ψ₁ w₀ = 0` on `SO(4)`. Going back through `Ψ₁` at the mode
   `j*`, `Φ^{(1)}_{j*}(w₀)(κ₀) = 0`, contradicting `hval`.
4. By `finsum_sign_two`, the function in the conclusion is the function of `hfin`.

So the top-weight argument replaces any closed formula for the chain: only the top mode of the
middle block survives the window, and it is a multiple of a single explicit function.

## Test functions (section TestFunctions)

For a block `b` of `GL₄` and vectors `u, u'`:

* `Gp hb u u' r m = G₊ = (yZ hb u)^r ν₊^m`, `Gm hb u u' r m = G₋ = (yZb hb u)^r ν₋^m` and
  `Fp = G₊ + G₋`. They lie in `Sm u u' r m` (`Gp_mem_Sm`, `Gm_mem_Sm`) and in `PF 4`
  (`yZ_mem_PF`, `yZb_mem_PF`, `nup_mem_PF`, `num_mem_PF`, `Fp_mem_PF`).
* Double flips (`pl_fl`, `w_fl30`, `w_fl31`, `w_fl32`, `nu_fl30`, `nu_fl31`, `nu_fl32`,
  `colv_fl3fl`, the `*_apply` lemmas, `yZ0_fl30`, `yZ0_fl31`, `yZ0_fl32`, `yZ2_fl30`,
  `yZ2_fl31`, `yZ2_fl32`): the effect of `s₃ s_i` on the column and Plücker functions. For
  example `s₃ s₂` fixes `w₁` and changes the signs of `w₂, w₃`, and `s₃ s₀` exchanges `ν₊` and
  `-ν₋`.
* `isSignEq_Fp0`: `detExt (Fp h40 u u' r m)` has the sign exponents `(r + m, 0, m, 0)`.
  `isSignEq_Fp2`: `detExt (Fp h42 u u' r m)` has `(m, 0, r + m, 0)`. Both follow from
  `isSignEq_detExt` and the double flips.
* Two modes (`expMode_one_pow_mul`, `expMode_neg_one_pow_mul`, `Fp0_rot0`, `Fp0_rot2`, `Fp2_rot0`,
  `Fp2_rot2`): `Fp h40` has the two modes `±(r + m)` along `r₀` and `±m` along `r₂`, with
  coefficients `G₊` and `G₋`. `Fp h42` has `±m` along `r₀` and `±(r + m)` along `r₂`.

## Test vectors (section TestVector)

* `exists_test_of` (**test vectors**): let `G ∈ PF 4`, and let `detExt G` have sign exponents `Q`
  with `(-1)^{Q₀} = (-1)^{|m(d)| + 1}`, `(-1)^{Q₁} = 1`, `(-1)^{Q₂} = (-1)^{|m(e)| + 1}` and
  `(-1)^{Q₃} = 1`. These are the values at `-1` of the position characters of `[d, e]`. Let `G`
  have two modes `±N₀` along `r₀` with `|N₀| ≥ |m(d)|`, and `±N₂` along `r₂` with `|N₂| ≥ |m(e)|`.
  Then some `v ∈ KF 4 [induced d, induced e]` equals `detExt G` on `O(4)`. Proof: `exists_KF`
  (`RealBlockFlatJacquet`). The windows come from `coeff_detExt_eq_zero`.
* `test_two_mode`: such a `v` has, through every point of `SO(4)`, the two modes of `G` along the
  block (`detExt_of_det_one`).

The module compiles with no errors or warnings.

## Provenance

Internal to the proof of `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`. The test functions are products of a complex coordinate of one column and
self-dual Plücker coordinates of two columns. They were chosen so that the middle block has a
one-dimensional space of top modes on `Sm` (`hasExpTop_Sm1`), and so that their modes along the
blocks `0` and `2` lie outside the windows of the two induction blocks. This makes the
nonvanishing of the chain explicit and avoids closed formulas (Krawtchouk-type identities) for
the multipliers.
