# Interlaced induction blocks: generic lemmas for the chain of multipliers

Lean module: `Langlands.Representation.Archimedean.RealInterlacedChain`, namespace
`Langlands.Archimedean.RealInterlacedJacquet`.

Third of the six modules that prove `RealInterlacedInducedInducedLinkedJacquetFunctionalStatement`
(see `RealInterlacedMirror.md`). It imports `RealInterlacedColumns`. The notation is that of
`RealInterlacedJacquet.md` and `RealInterlacedColumns.md`. `SO(n)` is `SOset n`.

## Binomial Fourier coefficients (section Binomial)

* `expMode_pow`, `expMode_neg_arg`: `(e^{ikt})^l = e^{ikl t}` and `e^{ik(-t)} = e^{-ikt}`.
* `coeff_binom`: for `σ ≠ 0` and `j ≤ N`, the coefficient at `σ j` of `t ↦ (a e^{iσt} + b)^N` is
  `2π C(N, j) a^j b^{N-j}`. Proof: binomial expansion and `coeff_finset_sum_nat`.

## Sign matrices of `GL₄` (section Signs)

* `fl i = s_i` is the diagonal sign matrix with `-1` at `i`. `signReflection_val4` identifies it
  with the Library's `signReflection 4 i`.
* `fl_mul_fl`, `fl_mul_fl_mul`, `fl_comm`, `det_fl_mul`: `s_i² = 1`, the `s_i` commute, and
  `det(s_i X) = -det X`.
* `colv_fl`: `s_j` changes the sign of the `j`-th entry of `X u`.
* `isSignEq_of_flips`: if `F(s_i X) = (-1)^{q_i} F(X)` for each `i`, then `IsSignEq q F` (the sign
  behaviour of `RealBlockFlatJacquet`).
* `det_eq_one_or_neg_one`: `det κ = ±1` on `O(n)`.
* `fl3_rot0`, `fl3_rot2`: `s₃ r₀(φ) = r₀(φ) s₃` and `s₃ r₂(φ) = r₂(-φ) s₃`.

## Extension from `SO(4)` by the determinant (section DetExt)

* `detExt G (X) = ((1 + det X)/2) G(X) + ((1 - det X)/2) G(s₃ X)`. On `O(4)` it is `G` on `SO(4)`
  (`detExt_of_det_one`) and `G(s₃ ·)` on the other component (`detExt_of_det_neg_one`).
* `detExt_mem_PF`: `detExt` preserves `PF 4`.
* `isSignEq_detExt`: if `G(s₃ s_i X) = (-1)^{q_i} G(X)` for `i = 0, 1, 2` and `q₃` is even, then
  `IsSignEq q (detExt G)`. The case `i = 3` uses `s₃ s₃ = 1`.
* `coeff_detExt_eq_zero`: if `G(r_b(φ) X) = e^{iNφ} A(X) + e^{-iNφ} B(X)` for `b = 0` or `b = 2`,
  then for `κ ∈ O(4)` the coefficients of weight `|k| < |N|` of `φ ↦ detExt G (r_b(φ) κ)` vanish.
  On the component of determinant `-1` this uses `fl3_rot0` or `fl3_rot2`.

These functions on `O(4)` are the restrictions of the test vectors (`exists_test_of` in
`RealInterlacedEngine`, through `exists_KF` of `RealBlockFlatJacquet`).

## Frobenius maps on `SO(n)` (section Frob)

Here `ℓ_μ = blockJacquet n ds' b μ` is a real Jacquet functional `hJ` and `Ψ = frobMap hJ`.

* `frobMap_eq_on` (**a step of the chain**): if `w = H` on `SO(n)` with `H ∈ S` and
  `HasExpTop b N S T`, then `Ψ w = H'` on `SO(n)` for some `H' ∈ S`. This is `exists_step`
  (`RealInterlacedColumns`) with `frobFun_apply_of_mem` (Library).
* `blockFourierCoefficient_eq_zero_of_frobMap`: if `Ψ w` vanishes on `SO(n)`, then
  `Φ^{(b)}_j(w)(κ) = 0` for `κ ∈ SO(n)` and every `j` with `μ_j ≠ 0`. The `j`-th coefficient of
  `θ ↦ (Ψ w)(r_b(θ) κ)` is `μ_j Φ_j(w)(κ)` (`blockFourierCoefficient_frobFun`, Library).
* `blockFourierCoefficient_eq_zero_of_eq_on`: a function vanishing on `SO(n)` has vanishing block
  Fourier coefficients there.

## Modes at the middle block of `GL₄` (section Middle)

* `sign_mem_SOset`, `sign_val`: `s₃ s₂ κ ∈ SO(4)` for `κ ∈ SO(4)`.
* `blockFourierCoefficient_neg_one`: for `w ∈ KF 4 (PL τ e)`,
  `Φ^{(1)}_{-j}(w)(g) = (-1)^{e₂ + e₃} Φ^{(1)}_j(w)(s₃ s₂ g)`. Proof: the Library's
  `blockFourierCoefficient_signReflection_mul_of_mem` and `_of_not_mem` (a sign matrix at a
  position of the block reverses the mode, one outside it keeps it; each contributes its
  character value `(-1)^{e_i}`), with `PL_position_neg_one`.
* `blockFourierCoefficient_one_eq_zero` (**only the modes `±N` at the middle block**): let
  `w ∈ KF 4 (PL τ e)` agree on `SO(4)` with a function having an expansion of order `N` along the
  block `1`. Assume that the window `|j| + 1 < N` of `w` at the block `1` vanishes on `O(4)`, and
  that `N ≡ par h41 e (mod 2)`. Then `Φ^{(1)}_j(w)(κ) = 0` for `κ ∈ SO(4)` and `j ≠ ±N`. Proof:
  modes with `|j| > N` vanish by the expansion
  (`blockFourierCoefficient_eq_of_expansion`), modes `|j| < N - 1` by the window, and modes
  `|j| = N - 1` by parity (`blockFourierCoefficient_eq_zero_of_not_even`, Library).

The module compiles with no errors or warnings.

## Provenance

Internal to Task 7070, built on the Library's block Fourier coefficients and Frobenius functions
(`RealBlockJacquetFunctional`, `RealJacquetFrobenius`) and on Worker 5731's `frobMap`.
