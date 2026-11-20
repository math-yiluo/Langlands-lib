# The Whittaker expansion of a smooth cuspidal function, standard character

Module `Langlands.Global.SmoothWhittakerExpansion.Expansion`, namespace
`Langlands.Global.SmoothWhittakerExpansion`. This helper module belongs to the proof of
`Langlands.Global.WhittakerExpansionStatement`. It proves the Whittaker expansion and its
locally uniform majorants for the standard character `m = (1, …, 1)`. The input is a
finite-smooth function `f₀` on `GL_{r+1}(F) \ GL_{r+1}(𝔸)` whose enveloping derivatives are
cuspidal and of exponential torus growth. The analytic work is done by the Library's Whittaker
expansion core (`Global.RankinSelberg.WhittakerExpansionCore`). This module builds the core's
input, a `WhittakerDecayClass`, from the space of enveloping derivatives of `f₀`. The
construction follows `Unfolding.cuspidalWhittakerExpansion` (module `ExpansionRealization`),
with the cyclic space of derivatives of one function in place of the space of an operator
realization.

Notation. `Points F n` is the group of adelic points of the general linear group scheme
`Scheme F n`. `homeo = GeneralLinearGroupPoints.adelicHomeomorph F n : Points F n → GL_n(𝔸)`
is the Library homeomorphism to the matrix group. `matrixGenerator F n Z` is the
enveloping-algebra element of a real archimedean matrix `Z`. `archPoint F n Z hZ` is the point
with archimedean component `1 + Z` (for `Z * Z = 0`) and finite component `1`. The file sets
`backward.isDefEq.respectTransparency false` and declares local `IsAffine` and `AddCommGroup`
instances, which are the Library's. These change no statement.

## Archimedean derivatives (section `Slice`)

* `smoothDifferential_finiteSmoothSlice`: the left-invariant derivative along `Z` of the
  archimedean slice of `w` at a finite point `y` is the value at `x_∞ · y` of the enveloping
  derivative `matrixGenerator Z · w`. Proof: `finiteSmoothSlice_envelopingAction` and
  `ArchimedeanGL.envelopingAction_real_generator`.
* `hasDerivAt_finiteSmooth_squareZero`: for `Z * Z = 0`, the derivative at `t = 0` of
  `t ↦ w(g · (1 + t Z)_∞)` is `(matrixGenerator Z · w)(g)`. Proof: write `g` as its archimedean
  part times its finite part. The curve then lies in the slice at `g_f`, and the Library's
  `hasDerivAt_smooth_squareZero` applies with the previous item.

## Group-scheme functions (section `SchemeFunction`)

* `schemeFunction F n` is the complex-linear map from `FiniteSmoothRationalFunctions F n` to
  functions on `Points F n`. It sends `w` to the evaluation of the group-scheme function
  `(continuousGeneralLinearEquiv F n).symm w`. By `schemeFunction_apply` it equals
  `x ↦ w(homeo x)`, via the Library's `evaluate_continuousGeneralLinearEquiv_at_point`.
* `schemeFunction_injective`, `continuous_schemeFunction`, `schemeFunction_rational_mul`:
  the map is injective, its values are continuous, and they are left invariant under the
  rational points (`Unfolding.continuous_evaluate`, `Unfolding.evaluate_rational_mul`).
* `schemeFunction_deriv`: the derivative at `t = 0` of `t ↦ schemeFunction w (x · archPoint (t Z))`
  is `schemeFunction (matrixGenerator Z · w) x`. This follows from
  `hasDerivAt_finiteSmooth_squareZero` and `adelicHomeomorph_archPoint`.

## The space of derivatives (section `Derivatives`)

* `derivatives F f₀` is the range of `u ↦ u · f₀`, a complex subspace of finite-smooth
  functions. It contains `f₀` (`self_mem_derivatives`) and is stable under the enveloping
  action (`envelopingAction_mem_derivatives`).
* `derivativeEnd F f₀ a` is the restriction of the action of `a` to this subspace. It is
  additive and complex-homogeneous in `a`.
* `decaySpace F f₀` is the image of `derivatives F f₀` under `schemeFunction`, a subspace of
  `Points F n → ℂ`. `decayEquiv F f₀` is the linear equivalence of the two subspaces, by
  injectivity. Every element of `decaySpace` is `schemeFunction (u · f₀)` for some `u`
  (`exists_eq_envelopingAction`).
* `decayDerivative F f₀ : ArchimedeanMatrix F n →ₗ[ℝ] decaySpace →ₗ[ℂ] decaySpace` conjugates
  `derivativeEnd (matrixGenerator Z)` by `decayEquiv`. It is real-linear in `Z` by
  `matrixGenerator_add` and `matrixGenerator_smul`.

## The decay class and the expansion (section `DecayClass`)

Assume `[CompactSpace (AdeleQuotient F)]` and let `f₀ : FiniteSmoothRationalFunctions F (r + 1)`.
The hypotheses are `hcusp` (every `u · f₀` is cuspidal), `0 ≤ c` and `hgrowth`: for every `u`
and compact `Q` some `C` satisfies `‖(u · f₀)(torInf x · q)‖ ≤ C · exp (c ∑ |x_i|)` for all `x`
and all `q ∈ Q`. These are the hypotheses of `exists_band_bound` in
`SmoothWhittakerExpansion.Decay`.

* `whittakerDecayClass_decaySpace`: `decaySpace F f₀` with `decayDerivative F f₀` is a
  `WhittakerDecayClass F r`. The five fields are proved as follows.
  - Continuity and rational invariance come from the `SchemeFunction` section.
  - The common finite level is `exists_common_level f₀`, transported by
    `adelicHomeomorph_finitePoint`.
  - Boundedness on determinant bands is `exists_band_bound` for the derivative `u` with
    `v = schemeFunction (u · f₀)`.
  - The square-zero derivatives are `schemeFunction_deriv`.
* `hasWhittakerMajorants_schemeFunction`: for a standard additive character `ψ`, the function
  `schemeFunction f₀` has locally uniform summable majorants of its Whittaker terms at every
  level `j ≤ r` (`HasWhittakerMajorants`). This is half (S) of the core,
  `whittakerMajorantsStatement_proof`, applied to the decay class and the vector `f₀`.
* `hasSum_whittaker_schemeFunction`: for every `x`,
  `∑_{q ∈ N_r(F) \ GL_r(F)} W(diag(γ_q, 1) x) = schemeFunction f₀ x`, where `W` is the
  standard Whittaker function `whittaker F r ψ` and `γ_q = q.out`. This is half (E) of the
  core, `hasSum_whittaker_of_levelPropsB`. Its summability input is the majorants at the
  singleton `{x}`. Its top-level input `LevelPropsB` comes from the Library's
  `CuspidalWhittaker.levelProps_top`, applied to the cuspidal function `f₀ = 1 · f₀`.

For the standard character this is the Whittaker expansion of Getz–Hahn, Theorem 11.3.6
(Cogdell 2004, Theorem 1.1), for smooth cuspidal functions whose enveloping derivatives are
cuspidal and of exponential torus growth. The reduction from a general character
`(ψ, m)` and the verification of these hypotheses are done in `SmoothWhittakerExpansion.Assembly`.
