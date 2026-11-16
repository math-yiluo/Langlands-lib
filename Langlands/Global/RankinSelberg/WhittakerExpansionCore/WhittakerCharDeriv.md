# Character derivatives of Whittaker functions

Module `Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerCharDeriv`, namespace
`Langlands.Global.RankinSelbergGlobal.Unfolding`. These are helper lemmas for half (S) of the
Whittaker expansion (see `Interface`). Differentiating `W_f(diag(γ, I) y ·)` along a suitable
square-zero archimedean direction multiplies it by `2πi L`. Here `L` is a real trace of the last
row of `γ` against the direction. This is the archimedean step of the decay argument for
Whittaker functions (compare Cogdell 2004, *Analytic theory of L-functions for GL_n*, §1, and
Shalika 1974, §5). The concrete matrix computations below are this project's own.

## Section `Geometry`

* `archCoord y ∈ GL_n(F_∞)` is the archimedean component of the adelic point `y`, in the mixed
  coordinates of `ArchimedeanGL`.
* `infCol w`, for a column `w` of elements of the mixed space `F ⊗ ℝ`, is the column of adeles
  with archimedean components `w_a` and finite components `0`.
* `colConj j y w = y_∞⁻¹ colMatrix_j(w) y_∞`, with `y_∞ = archCoord y`.
* `colConj_mul_self`: `colConj j y w` has square zero, because `colMatrix_j(w)² = 0`
  (`colMatrix_mul_colMatrix`).
* `isColSupported_infCol`: `infCol` preserves support in the first `j + 1` coordinates.
* `archCoord_colPoint_infCol`, `finite_colPoint_infCol`: the column point
  `colPoint(infCol w) = 1 + colMatrix_j(infCol w)` has archimedean component `1 + colMatrix_j(w)`
  and finite component `1`. Proof: entrywise computation.
* `colMatrix_smul`: `colMatrix_j(t w) = t colMatrix_j(w)` for real `t`.
* `colPoint_infCol_mul`: `colPoint(infCol(t w)) y = y archPoint(t colConj j y w)`. Proof: compare
  archimedean and finite components (`AdelicGL.ext_infinite_finite`). The archimedean identity is
  `(1 + t C) y_∞ = y_∞ (1 + t y_∞⁻¹ C y_∞)`, and both finite components equal `y_f`.

## Section `Character`

* `standardCharacter_sum_infCol`: for `b ∈ F`, `ξ ∈ F^{r+1}` and a column `w`,
  `ψ₀(b Σ_a ξ_a infCol(t w)_a) = 𝐞(t Tr(b Σ_a ξ_a w_a))`. Here `ψ₀` is the Library's
  `EqualAnalytic.standardCharacter`, `Tr` is the archimedean trace `mixedTrace`, and
  `𝐞(x) = exp(2πix)`. Proof: the sum is the infinite adele of `t Σ_a ξ_a w_a`. Then apply the
  Library's `standardCharacter_mul_infiniteAdele`.
* `hasDerivAt_fourierChar_mul`: `t ↦ 𝐞(t L)` has derivative `2π L i` at `0`, by the chain rule for
  the complex exponential.

## Section `Identity`

Assume that `(V, R)` is a `WhittakerDecayClass` and that `ψ` is a standard additive character.
Assume also `ψ(x) = ψ₀(b x)` for some `b ∈ F`. The Library's `exists_eq_standardCharacter_mul`
supplies such a `b`.

* `padRow g0 ∈ F^{r+1}` is the last row of `γ = g0 ∈ GL_{j+1}(F)`, padded by zeros.
* `colFrequency b ξ w = Tr(b Σ_a ξ_a w_a)`.
* `whittaker_deriv_eq`: let `j < r`, `γ ∈ GL_{j+1}(F)`, and let `w` be supported in the first
  `j + 1` coordinates. Set `Z = colConj j y w`. Then
  `W_{R_Z f}(diag(γ, I) y) = 2π L i · W_f(diag(γ, I) y)` with `L = colFrequency b (padRow γ) w`.

  Proof. By `hasDerivAt_whittaker`, which uses the decay-class axioms, the left side is the
  derivative at `0` of `t ↦ W_f(diag(γ, I) y archPoint(tZ))`. By `colPoint_infCol_mul`, this
  function equals `t ↦ W_f(diag(γ, I) colPoint(infCol(t w)) y)`. By
  `whittaker_padRational_colPoint` and `standardCharacter_sum_infCol`, it is
  `t ↦ 𝐞(t L) W_f(diag(γ, I) y)`. Derivatives are unique, and `hasDerivAt_fourierChar_mul` gives
  the value.
* `whittaker_pow_deriv_eq`: the `K`-fold iterate,
  `W_{(R_Z)^K f}(diag(γ, I) y) = (2π L i)^K W_f(diag(γ, I) y)`. Proof: induction on `K`. The
  direction `Z` and the frequency `L` do not depend on `f`.
