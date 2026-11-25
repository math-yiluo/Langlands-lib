# Partial Euler factorization of the equal-rank dual global Whittaker integral

`Langlands.Global.RankinSelbergGlobal.EqualDualEulerFactorizationStatement` is the partial
Euler factorization, at the unramified places, of the global Rankin–Selberg Whittaker
integral `Ψ(s; W̃, W̃', Φ̂)` on the dual side of the equal-rank global functional
equation. The partial L-function in it is the one of the contragredient pair. It is a
Prop-valued statement. Nothing here proves it. It is the equal-rank companion of
`UnequalDualEulerFactorizationStatement` and the dual companion of
`EqualEulerFactorizationStatement`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3).

* §2.3, Theorem 2.2 and the remark after it, printed p.211 (PDF p.214): the right-hand
  side of the global functional equation unfolds as
  `I(1 − s; φ̃, φ̃', Φ̂) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W̃_φ(g) W̃'_φ'(g) Φ̂(e_n g) |det g|^(1−s) dg = ∏_v Ψ_v(1 − s; W̃_(φ_v), W̃'_(φ'_v), Φ̂_v)`,
  "with convergence for `Re(s) ≪ 0`". Here `φ̃(g) = φ(w_n ᵗg⁻¹)` (p.207) and
  `W̃(g) = W(w_n ᵗg⁻¹)`.
* §2.3, printed p.210 (PDF p.213): the factorization of `Ψ(s; W, W', Φ)` into the local
  integrals `Ψ_v(s; W_v, W'_v, Φ_v)` for decomposable data, with convergence for
  `Re(s) ≫ 0`. The same argument applies to the integral of `W̃`, `W̃'`, `Φ̂`.
* Theorem 3.3, printed p.215 (PDF p.218): if `π_v`, `π'_v` and `ψ_v` are unramified,
  `W_o ∈ 𝒲(π_v, ψ_v)` and `W'_o ∈ 𝒲(π'_v, ψ_v^(−1))` are the normalized
  `GL_n(𝒪_v)`-fixed Whittaker functions and `Φ_o = 1_(𝒪_v^n)`, then
  `Ψ_v(s; W_o, W'_o, Φ_o) = L(s, π_v × π'_v) = det(I − q_v^(−s) A_(π_v) ⊗ A_(π'_v))^(−1)`.
* §4.1, proof of Theorem 4.1, printed pp.219–220 (PDF pp.222–223): both sides of the
  global functional equation are factored as a product over the places of `S` times a
  partial L-function. For the dual side this partial L-function is `L^S(1 − s, π̃ × π̃')`.
  Cogdell writes the argument out for `m < n` and says that the equal-rank case is
  "entirely analogous" (p.220).

## The statement

`F`, `ψ`, `n = r + 1`, `T`, `T'` and `S` are as in `EqualEulerFactorizationStatement`:
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` is trivial on `F`, `T`, `T'`
are actual cuspidal realizations of `GL_n`, and `S` is a finite set of finite places with
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`. In addition:

* `Td`, `Td'` are actual cuspidal realizations of `GL_n` with
  `Automorphic.OperatorRealization.IsContragredientOf Td.realization T.realization` and
  the same for `Td'`, `T'`. So `Td` realizes `π̃` and `Td'` realizes `π̃'` (module
  `Langlands.Automorphic.Contragredient`).
* `Pd`, `Pd'` are spectral presentations of `Td`, `Td'` (universe `uQ`) with exceptional
  sets contained in `S`.

Then there exists `σ : ℝ` with the following property. Take any `x : T.Space`,
`x' : T'.Space` with `IsSphericalOutside`, that is, fixed by `GL_n(𝒪_v)` at every finite
`v ∉ S`, and any `Φ ∈ schwartzBruhat F n` with `IsStandardOutside F n S Φ`. Set

* `Wdual = dualFunction F n (cuspWhittaker F T ψ.complex x)`, the function
  `g ↦ W(w_n ᵗg⁻¹)`, that is, `W̃`;
* `W'dual = dualFunction F n (cuspWhittaker F T' ψ.complex⁻¹ x')`, that is, `W̃'`;
* `Φhat = fourierTransform F n ψ.complex Φ`, the Fourier transform `Φ̂` for the
  covolume-one Haar measure `rectangleMeasure F 1 n` (module
  `Langlands.Global.RankinSelberg.SchwartzBruhat`).

These are exactly the functions in the dual half of the published
`EqualUnfoldingStatement`. Then for every `s` with `σ < Re s`:

1. `equalWhittakerIntegrand F Wdual W'dual Φhat s` is integrable for
   `whittakerQuotientMeasure F n`. This is absolute convergence of `Ψ(s; W̃, W̃', Φ̂)`.
2. `∑_(v ∉ S) ‖L̃_v(s) − 1‖` converges, where
   `L̃_v(s) = partialEulerFactor Pd Pd' hPd hPd' v s`.
3. There is `p` with `HasProd (fun v => L̃_v(s)) p` and
   `equalWhittakerIntegral F Wdual W'dual Φhat s = partialEqualWhittakerIntegral F S Wdual W'dual Φhat s * p`.

The source evaluates the dual side at `1 − s` with `Re s ≪ 0`. In the variable of this
statement that is the right half-plane `σ < Re s`. Every convergence claim is in the
conclusion, and no binder supplies an integral, its value or its convergence. The module
declares the same two local instances as `EqualEulerFactorizationStatement`: the
Library's theorems `GroupScheme.GeneralLinear.isAffine_groupScheme` and
`GroupScheme.GeneralLinear.smoothStatement` made available to instance search. They add
no hypothesis.

## Normalizations and comparison with the source

* **Contragredient spectra.** `W̃ = dualFunction F n W` lies in the `ψ⁻¹`-Whittaker model
  of `π̃`, and `W̃'` lies in the `ψ`-Whittaker model of `π̃'`. Theorem 3.3 applies with
  `ψ_v` replaced by `ψ_v^(−1)`, which is again unramified. So at `v ∉ S` the local factor
  is `L(s, π̃_v × π̃'_v)`. The spectra of `Pd`, `Pd'` at `v ∉ S` are the Satake parameters
  of the local components of `Td`, `Td'`, that is, of `π̃_v` and `π̃'_v`, because `Td` and
  `Td'` are irreducible. So `partialEulerFactor Pd Pd'` is the factor
  `det(I − q_v^(−s) A_(π̃_v) ⊗ A_(π̃'_v))^(−1)`, with the Satake normalization of
  `EqualEulerFactorizationStatement` (Gross (1998), (3.14), through
  `Unramified.standardHeckeScalar`). Presenting the contragredients through their own
  realizations and presentations avoids any Library comparison of the spectra of `T`
  and `Td`.
* **Spherical vectors.** `W̃(g u) = W(w_n ᵗg⁻¹ ᵗu⁻¹)`, and `ᵗk⁻¹ ∈ GL_n(𝒪_v)` for
  `k ∈ GL_n(𝒪_v)`. So `W̃` is right `GL_n(𝒪_v)`-invariant at every finite `v ∉ S` when
  `x` is spherical there, and its normalized local component is
  `W̃_(o,v)(g) = W_(o,v)(w_n ᵗg⁻¹)`, with `W̃_(o,v)(e) = W_(o,v)(w_n) = 1` because
  `w_n ∈ GL_n(𝒪_v)`. The same holds for `W̃'`.
* **`Φ̂` is standard outside `S`.** The statement assumes `IsStandardOutside` for `Φ`, not
  for `Φ̂`. It follows. By Tate's thesis, `rectangleMeasure F 1 n` (covolume one) is the
  product of the local measures self-dual for `ψ_v` (see the Markdown of
  `SchwartzBruhat`). For `v ∉ S` the character `ψ_v` has conductor `𝒪_v`
  (`FiniteAdditiveSupport`), so the self-dual measure on `F_v^n` gives `𝒪_v^n` volume one
  and `(1_(𝒪_v^n))^ = 1_(𝒪_v^n)`. Hence for a pure tensor
  `Φ = Φ_(S∪∞) ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`, `Φ̂ = Φ̂_(S∪∞) ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)`. A general `Φ`
  with `IsStandardOutside F n S Φ` is a finite sum of such pure tensors (Markdown of
  `EqualEulerFactorizationStatement`), and the Fourier transform is linear.
* **The partial integral.** `partialEqualWhittakerIntegral` restricts to the classes
  whose components at `v ∉ S` lie in `N_n(F_v) GL_n(𝒪_v)`. On that set, for `g_v = u_v k_v`,
  `W̃_(o,v)(g_v) W̃'_(o,v)(g_v) = 1`, `Φ̂_v(e_n g_v) = 1_(𝒪_v^n)(e_n k_v) = 1` and
  `|det g_v| = 1`. So, as in `EqualEulerFactorizationStatement`, `Ψ_(S∪∞)(s; W̃, W̃', Φ̂)` is
  the global measure constant times the local integrals at `S ∪ ∞` times the local
  volumes of `N_n(F_v) \ N_n(F_v) GL_n(𝒪_v)`. The full integral is the same constant times
  the local integrals at `S ∪ ∞` times the unramified local integrals
  `Ψ_v(s; W̃_(o,v), W̃'_(o,v), 1_(𝒪_v^n)) = L(s, π̃_v × π̃'_v)` times the same local volumes.
  The identity therefore holds for every normalization of `whittakerQuotientMeasure`.
* **Vectors, uniformity, `S`.** These are as in `EqualEulerFactorizationStatement`. The
  conditions `IsSphericalOutside` are imposed on `x ∈ T` and `x' ∈ T'`, the data of the
  ordinary side, as in the published `EqualUnfoldingStatement`. Both sides of the
  identity are linear in `x`, `x'` and `Φ`. `σ` is chosen before the vectors and `Φ`. It
  may depend on `ψ`, `T`, `T'`, `Pd`, `Pd'` and `S`.

## Deviations from the source

* Cogdell states the factorization on the dual side only implicitly ("entirely
  analogous", p.220). This statement makes it explicit for the equal-rank case. The
  consumer is the proof of the partial functional equation
  `Langlands.Global.CuspidalPairPartialGammaEquationStatement`.
* Cogdell obtains the unramified dual local integral from Theorem 3.3 applied to the
  contragredient pair. The statement asserts only the global identity, so a proof may
  use that route or the local functional equation.
* `HasIrreducibleAdmissibleComponents` is not assumed, as in
  `EqualEulerFactorizationStatement`. Only the places `v ∉ S` enter.
* Cogdell's `S` contains the archimedean places. Here `S` is finite and the infinite
  places are always kept in `Ψ_(S∪∞)`.

## Provenance

The statement transcribes Cogdell pp.210–211, 215 and 219–220 onto the Library's actual
realizations, contragredient realizations, spectral presentations, the Schwartz–Bruhat
space and its Fourier transform, and the published equal-rank Whittaker integrals of
`Langlands.Global.RankinSelberg.EqualIntegrals` and
`Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral`. Its form copies
`EqualEulerFactorizationStatement`, with the functions of the dual half of
`EqualUnfoldingStatement` and the presentations `Pd`, `Pd'` of the contragredients, as
`UnequalDualEulerFactorizationStatement` does for unequal ranks. The arguments above for
the spherical vectors and for `Φ̂` are standard computations that explain why the
identity holds as stated. They are not part of the Lean statement.
