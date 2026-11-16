# Archimedean local Rankin–Selberg integrals

Module `Langlands.Global.RankinSelberg.ArchimedeanIntegrals`, namespace
`Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal`. It defines the local integrals of
Jacquet 2009, formulas (2.4)–(2.6), p.6, over `ℝ` and `ℂ`, for the statements
`ArchimedeanFunctionalEquationStatement` and `ArchimedeanFactorizationStatement`. It contains
definitions only.

The names `rectangularPoint`, `unfoldingWeyl`, `dualFunction`, `translateFunction` and
`fourierTransform` also exist, for adelic points, in the namespace
`Langlands.Global.RankinSelbergGlobal`. The local versions live in the sub-namespace
`ArchimedeanLocal` and use the same coordinates. Modules that use both qualify the local
names.

## Generic definitions

Let `K` be a field, `nabs : K → ℝ` an absolute value given as a function, `n = r + 1` and
`m = t + 1`. `LeftUnipotentQuotient t K` is the Library's quotient `N_m(K) \ GL_m(K)`; the
integrands are evaluated at the representative `q.out` of a class `q`. The integrands are
left `N_m`-invariant because `W` and `W'` are Whittaker functions for inverse characters.

* `detPower nabs g s = exp(s · log nabs(det g))`, that is `nabs(det g)^s`.
* `unequalIntegrand nabs h W W' s q = W(diag(g, 1_(n−m))) W'(g) nabs(det g)^(s − (n−m)/2)`
  for `g = q.out` and `t < r`. The embedding `g ↦ diag(g, 1)` is the Library's `padGL`.
* `rectangularPoint h g x = [[g, 0, 0], [x, 1_(n−m−1), 0], [0, 0, 1]]` for
  `x ∈ M_((n−m−1) × m)(K)`. It is built from `GeneralLinear.lowerBlockLocalization` in the
  same way as the global `rectangularPoint`.
* `unfoldingWeyl h = diag(1_m, w_(n−m))`, with `w_k = GeneralLinear.weylLong k K`, built as
  the global `unfoldingWeyl`.
* `dualFunction n W (g) = W(w_n ᵗg⁻¹)`, with `w_n = GeneralLinear.weylLong n K` and
  `ᵗg⁻¹ = GeneralLinear.inverseTranspose n K g`, as in the global `dualFunction`.
* `translateFunction a W (g) = W(g a)`, right translation `ρ(a)`.
* `blockKernel nabs h W W' s q x = W(rectangularPoint h g x) W'(g) nabs(det g)^(s − (n−m)/2)`,
  the integrand of Jacquet's (2.5) with `j = n − m − 1`.
* `equalIntegrand nabs W W' Φ s q = W(g) W'(g) Φ(e_n g) nabs(det g)^s`, where `e_n g` is the
  last row of `g` (the Library's `lastRow`), as in `equalWhittakerIntegrand`.
* `fourierTransform χ ν Φ (x) = ∫ Φ(y) χ(∑_j y_j x_j) dy`, for the product measure
  `Measure.pi (fun _ => ν)` on `K^n`. The sign is positive, as in the Library's global
  `fourierTransform`.
* `unequalIntegral nabs μ h W W' s = ∫ unequalIntegrand ... dμ`, Jacquet's `Ψ(s; W, W')`
  (2.4), for a measure `μ` on the quotient.
* `blockIntegral nabs μ ν h W W' s = ∫ (∫ blockKernel ... dx) dμ`, Jacquet's
  `Ψ_(n−m−1)(s; W, W')` (2.5). The inner variable `x` is integrated first, with the product
  measure `rectangularMeasure ν (n−m−1) m` of `ν`.
* `equalIntegral nabs μ W W' Φ s = ∫ equalIntegrand ... dμ`, Jacquet's `Ψ(s; W, W', Φ)`
  (2.6).

## Quotient measures

`QuotientMeasureData t K` bundles a Haar measure on `GL_m(K)`, a right-invariant Haar
measure on `N_m(K)` and a measure `measure` on `N_m(K) \ GL_m(K)` that is compatible with
them in the sense of the Library's `QuotientIntegration.IsCompatible`, i.e. the Weil
integration formula holds. Such a measure is a right-invariant quotient measure. Any two are
proportional, since Haar measures are unique up to a positive constant and `IsCompatible`
determines the quotient measure.

`ComplexQuotientMeasureData t` and `RealQuotientMeasureData t` are this structure over `ℂ`
and over `ℝ`, with Borel measurable structures on `GL_m`, `N_m` and the quotient (local
instances `borel _`).

## Normalizations at a place

* **Absolute values.** `complexNormalizedAbs z = |z|²`, the normalized absolute value of `ℂ`;
  `realNormalizedAbs x = |x|`. The Library's generic local integrals take an
  `AbsoluteValue`, and `|z|²` is not one (it fails the triangle inequality), so the
  integrals here take a function.
* **Additive characters.** The archimedean component `ψ_v` of the global character is
  `realScaledCharacter a : x ↦ exp(2πi a x)` at a real place and
  `complexScaledCharacter a : z ↦ exp(2πi Tr(a z))` at a complex place
  (`IsRealAdditiveComponent`, `IsComplexAdditiveComponent`).
* **Self-dual measures.** `realSelfDualMeasure a = realScaledMeasure |a|^(1/2)`, i.e.
  `|a|^(1/2) dx`, and `complexSelfDualMeasure a = complexScaledMeasure |a|`, i.e.
  `|a| · 2 dx dy`. These are the measures self-dual for `realScaledCharacter a` and
  `complexScaledCharacter a`, and they are the normalizations used for `ε` in
  `UnequalSemilocalEquationStatement` (`√|a|` at a real place, `|a|` at a complex place).
  The Fourier transform and the inner variable of the dual block integral use them.

## Integrals at a place

For `D : ComplexQuotientMeasureData t` and `a ∈ ℂ^×` (complex place):

* `complexUnequalIntegrand h W W' s` and `complexUnequalIntegral h D W W' s`: `Ψ(s; W, W')`
  with `|·|²` and `D.measure`.
* `complexUnequalDualKernel h W W' s`, a function on the product of the quotient and the
  rectangular matrices: the kernel of `Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')`, with
  `ρ(w_(n,m)) W̃ = translateFunction (unfoldingWeyl h) (dualFunction (r+1) W)` and
  `W̃' = dualFunction (t+1) W'`.
* `complexUnequalDualMeasure a D = D.measure × rectangularMeasure (complexSelfDualMeasure a)`,
  the product measure on which this kernel is integrated.
* `complexUnequalDualIntegral h a D W W' s = Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')`, with the inner
  variable for `complexSelfDualMeasure a`.
* `complexFourierTransform a Φ`: `fourierTransform` for `complexScaledCharacter a` and
  `complexSelfDualMeasure a`.
* `complexEqualIntegrand W W' Φ s` and `complexEqualIntegral D W W' Φ s = Ψ(s; W, W', Φ)`.
* `complexEqualDualIntegral a D W W' Φ s = Ψ(s; W̃, W̃', Φ̂)` with
  `Φ̂ = complexFourierTransform a Φ`.

The real-place definitions `realUnequalIntegrand`, `realUnequalIntegral`,
`realUnequalDualKernel`, `realUnequalDualMeasure`, `realUnequalDualIntegral`,
`realFourierTransform`, `realEqualIntegrand`, `realEqualIntegral` and
`realEqualDualIntegral` are the same with `ℝ`, `|x|`, `realScaledCharacter a` and
`realSelfDualMeasure a` for `a ∈ ℝ^×`.

The integrals are Bochner integrals, so they are `0` where the integrand is not integrable.
The statements assert integrability on a right half-plane separately.

## Comparison with the sources

* **Jacquet 2009**, `jacquet-2009-archimedean-rankin-selberg`, p.6, (2.4)–(2.6): the
  integrals are his, with `W` in the Whittaker model for `ψ` and `W'` in the model for `ψ̄`
  (the overlines are lost in the text extraction of the posted file). His measure on the
  quotient is a fixed invariant measure; here it is any compatible quotient measure, the
  same in an integral and its dual. His Fourier transform (p.3) is
  `∫ Φ(Y) ψ(−Tr(ᵗX Y)) dY` for the self-dual measure, with a negative sign. Here the sign is
  positive, as in the Library's global `fourierTransform`. The effect on the sign of the
  functional equation is worked out in the Markdown of
  `ArchimedeanFunctionalEquationStatement`.
* **Jacquet's `w_n`, `W̃`** (p.4) are the long Weyl element and `W̃(g) = W(w_n ᵗg⁻¹)`, as here.
* **Cogdell 2004**, `cogdell-2004-analytic-theory-gln`, pp.216–217, writes the same integrals
  at an archimedean place with the integrals of Theorem 3.5.

## Provenance

Source definitions: Jacquet 2009, (2.4)–(2.6), p.6, in the coordinates and conventions of the
Library's global integrals (`Langlands.Global.RankinSelberg.WhittakerIntegrals`,
`UnequalIntegrals`, `EqualIntegrals`, `SchwartzBruhat`). `QuotientMeasureData` and the
wrappers at a place are internal packaging of Task 7136.
