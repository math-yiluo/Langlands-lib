# Exponential torus growth from uniform moderate growth on `GL_n`

Module `Langlands.Global.SmoothWhittakerExpansion.Growth`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. This helper module belongs to the proof of
`Langlands.Global.WhittakerExpansionStatement`. It turns the statement's growth hypothesis
`HasAdelicUniformModerateGrowth` into the growth hypothesis `hgrowth` of the band bounds in
`SmoothWhittakerExpansion.Decay`. It is internal to that proof.

The file sets `backward.isDefEq.respectTransparency false`. It declares local `IsAffine` and
`AddCommGroup` instances, which are the Library's instances, and changes no statement.

## Results

* `exists_torInf_le_of_submultiplicative`: let `H` be a continuous, nonnegative and
  submultiplicative function on the archimedean matrix group `InfiniteAdelicGL F n`
  (`H (g g') ≤ H g · H g'`). Then `H (torInf x) ≤ C₀ · exp (c₀ ∑ |x_i|)` for some
  `C₀, c₀ ≥ 0`.
  Proof: this is the argument of the Library's `exists_matrixHeight_torInf_le` for an arbitrary
  such `H`. Let `M₀ ≥ 1` bound `H ∘ torInf` on the cube `[-1, 1]^n`. Take
  `k = ⌈∑ |x_i|⌉ + 1` and `y = x / k`. Then `torInf x = (torInf y)^k` (`torInf_nsmul`), so
  submultiplicativity gives `H (torInf x) ≤ M₀^k ≤ M₀² · exp (log M₀ · ∑ |x_i|)`.
* `pos_of_isClosedSubgroup`: a closed matrix embedding `rho` of `GL_{r+1}` into `N × N`
  matrices has `N > 0`. Proof: for `N = 0` the target group `GL_0(𝔸)` is trivial. The Library
  embedding `isClosedEmbedding_adelicMatrix` is injective, so `GL_{r+1}(𝔸)` would be trivial.
  The rational scalar matrix `2 · 1` contradicts this.
* `exists_torus_growth` (main result): let `rho` be a matrix representation with `N > 0`,
  `hsmooth`, `hcalc` the smoothness data, and `φ` a finite plot-smooth function with
  `HasAdelicUniformModerateGrowth`. Then there is one rate `c ≥ 0` with the following property.
  For every `u` in the archimedean enveloping algebra and every compact `Q ⊆ GL_n(𝔸)`, some
  constant `C` satisfies
  `‖(u · φ')(torInf x · q)‖ ≤ C · exp (c ∑ |x_i|)` for all `x` and all `q ∈ Q`. Here
  `φ' = finitePlotSmoothGeneralLinearEquiv F n φ` is the matrix-side function of `φ`.
  Proof: `hasAdelicUniformModerateGrowth_iff` and
  `hasAdelicUniformPolynomialGrowth_iff_generalLinear` give one exponent `e` and, for each `u`,
  a constant `C_u` with `‖(u · φ')(g)‖ ≤ C_u · ht(g)^e`. Here `ht` is the Library adelic height
  of `rho` transported to `GL_n(𝔸)`. It is continuous, at least `1` and submultiplicative
  (`continuous_adelicHeight`, `one_le_adelicHeight`, `adelicHeight_mul_le`). The first result,
  applied to `ht ∘ ofInfinite`, bounds `ht (torInf x)` exponentially. Submultiplicativity with
  a bound `M` for `ht` on `Q` then gives
  `ht (torInf x · q) ≤ C₀ M · exp (c₀ ∑ |x_i|)`, and `c = e · c₀`.
