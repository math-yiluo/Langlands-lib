# Partial Euler factorization of the equal-rank global Whittaker integral

`Langlands.Global.RankinSelbergGlobal.EqualEulerFactorizationStatement` is the partial
Euler factorization, at the unramified places, of the global Rankin–Selberg Whittaker
integral `Ψ(s; W, W', Φ)` of a pair of cusp forms on `GL_n × GL_n` and a Schwartz–Bruhat
function `Φ` on `𝔸^n`. It is a Prop-valued statement. Nothing here proves it. It is the
equal-rank companion of `UnequalEulerFactorizationStatement`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF SHA-256 `8117f145…`, PDF page = printed page + 3).

* §2.3, printed p.210 (PDF p.213): after unfolding,
  `I(s; φ, φ', Φ) = Ψ(s; W_φ, W'_φ', Φ) = ∫_(N_n(𝔸) \ GL_n(𝔸)) W_φ(g) W'_φ'(g) Φ(e_n g) |det g|^s dg`,
  which "converges for `Re(s) ≫ 0`". If `φ`, `φ'` and `Φ` are decomposable tensors, with
  `W_φ(g) = ∏_v W_(φ_v)(g_v)`, `W'_φ'(g) = ∏_v W'_(φ'_v)(g_v)` and `Φ(g) = ∏_v Φ_v(g_v)`, then
  `Ψ(s; W_φ, W'_φ', Φ) = ∏_v Ψ_v(s; W_(φ_v), W'_(φ'_v), Φ_v)`, still for `Re(s) ≫ 0`.
* Theorem 3.3, printed p.215 (PDF p.218): if `π_v`, `π'_v` and `ψ_v` are all unramified,
  `W_o ∈ 𝒲(π_v, ψ_v)` and `W'_o ∈ 𝒲(π'_v, ψ_v^(−1))` are the `GL_n(𝒪_v)`-fixed Whittaker
  functions with `W_o(e) = W'_o(e) = 1`, and `Φ_o` is the characteristic function of
  `𝒪_v^n`, then `L(s, π_v × π'_v) = det(I − q_v^(−s) A_(π_v) ⊗ A_(π'_v))^(−1) = Ψ_v(s; W_o, W'_o, Φ_o)`.
* §4.1, proof of Theorem 4.1, printed p.219 (PDF p.222): for `m = n` and suitable
  `φ`, `φ'`, `Φ`,
  `I(s; φ, φ', Φ) = (∏_(v ∈ S) Ψ_v(s; W_(φ_v), W'_(φ'_v), Φ_v)) L^S(s, π × π')`, with
  `L^S(s, π × π') = ∏_(v ∉ S) L(s, π_v × π'_v)` absolutely convergent for `Re(s) ≫ 0`
  (p.218–219).

The local equal-rank computation is due to Jacquet and Shalika, *On Euler products and
the classification of automorphic forms I*, Amer. J. Math. 103 (1981), registered as
`provided-6d5abbbab517cf7269b6ab243e0d7a101940980b658f88cb722e13748f802ad4`,
Proposition (2.3), printed pp.511–512 (PDF pp.13–14): with `Φ` the characteristic
function of `𝒪^r` and the measures normalized by `vol(N ∩ K) = 1`, `vol(K) = 1`, the
integral of the essential Whittaker functions equals `L(s, π × π')`. Their proof uses
the Iwasawa decomposition, the formula of Shintani (and Casselman–Shalika) for the
essential Whittaker function, and the Cauchy identity
`∑_J Tr ρ_J(A) Tr ρ_J(A') X^(tr J) = det(1 − A ⊗ A' X)^(−1)`. The Library has no statement
of this equal-rank computation: `Langlands.RankinSelberg.UnramifiedPairIntegralStatement`
covers only unequal ranks, and its Markdown lists the equal-rank case as not stated.

## The statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`. Let
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` be trivial on `F`. This type
consists of the continuous, circle-valued, nontrivial additive characters, so
`ψ.complex` satisfies the hypothesis `IsStandardAdditiveCharacter` of the equal-rank
analytic and unfolding statements. Let `n = r + 1`. Let `T` and `T'` be actual cuspidal
realizations of `GL_n`, and let `P`, `P'` be spectral presentations of them (universe
`uQ` for the local factors). Let `S` be a finite set of finite places containing
`P.exceptional` and `P'.exceptional` and satisfying
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`: at every finite `v ∉ S` the
canonical local component of `ψ` exists and has conductor `𝒪_v`.

Then there exists `σ : ℝ` with the following property. Take any vectors `x : T.Space`,
`x' : T'.Space` with `IsSphericalOutside F T S x` and `IsSphericalOutside F T' S x'`, that
is, fixed by `GL_n(𝒪_v)` at every finite `v ∉ S`. Take any `Φ : RowVector F n → ℂ` with
`Φ ∈ schwartzBruhat F n` and `IsStandardOutside F n S Φ`. Set
`W = cuspWhittaker F T ψ.complex x` and `W' = cuspWhittaker F T' ψ.complex⁻¹ x'`, the
global Whittaker functions of the cusp forms for the standard characters of `ψ` and
`ψ⁻¹`. Then for every `s` with `σ < Re s`:

1. `equalWhittakerIntegrand F W W' Φ s` is integrable for `whittakerQuotientMeasure F n`.
   This is absolute convergence of `Ψ(s; W, W', Φ)`.
2. `∑_(v ∉ S) ‖L_v(s) − 1‖` converges, where
   `L_v(s) = partialEulerFactor P P' hP hP' v s`. This is absolute convergence of the
   Euler product.
3. There is `p` with `HasProd (fun v => L_v(s)) p` (the unconditional product over the
   finite places `v ∉ S`) and
   `equalWhittakerIntegral F W W' Φ s = partialEqualWhittakerIntegral F S W W' Φ s * p`.

The objects are:

* `schwartzBruhat F n` is the Schwartz–Bruhat space `S(𝔸^n)` and `IsStandardOutside F n S Φ`
  says that `Φ` vanishes off `∏_(v ∉ S) 𝒪_v^n` and, on that set, depends only on the
  coordinates at `S` and at the infinite places; that is, `Φ_v = 1_(𝒪_v^n)` for finite
  `v ∉ S` (module `Langlands.Global.RankinSelberg.SchwartzBruhat`).
* `equalWhittakerIntegrand` and `equalWhittakerIntegral` are the integrand
  `W(g) W'(g) Φ(e_n g) |det g|^s` and the integral `Ψ(s; W, W', Φ)` over
  `N_n(𝔸) \ GL_n(𝔸)` (module `Langlands.Global.RankinSelberg.EqualIntegrals`).
* `partialEqualWhittakerIntegral` is `Ψ_(S∪∞)`, the same integral over the classes whose
  components at `v ∉ S` lie in `N_n(F_v) GL_n(𝒪_v)` (module
  `Langlands.Global.RankinSelberg.PartialEqualWhittakerIntegral`).
* `partialEulerFactor P P' hP hP' v s = ∏_(i,j) (1 − a_i b_j q_v^(−s))^(−1)` (module
  `Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement`), where the
  multisets `a` and `b` are the spectra that `P` and `P'` supply at `v`.
* `IsSphericalOutside` is from `Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`;
  `cuspWhittaker` is from `Langlands.Global.RankinSelberg.UnequalIntegrals`.

Every convergence claim is in the conclusion, and no binder supplies an integral, its
value or its convergence. The module declares two local instances, as
`UnequalEulerFactorizationStatement` does. They record that the group scheme of `GL_n` is
affine and smooth, and they are the Library's theorems
`GroupScheme.GeneralLinear.isAffine_groupScheme` and `GroupScheme.GeneralLinear.smoothStatement`
made available to instance search. They add no hypothesis.

## Normalizations and comparison with the source

* **Local data outside `S`.** Let `x`, `x'` and `Φ` be pure tensors whose components at
  every finite `v ∉ S` are spherical, and let `Φ_v = 1_(𝒪_v^n)` there. Then
  `W(g) = W_(S∪∞)(g_(S∪∞)) ∏_(v ∉ S) W_(o,v)(g_v)` with every `W_(o,v)(e) = 1`, and similarly
  for `W'`; the scalars are absorbed into the factor at `S ∪ ∞`. On the set selected by
  `unipotentIntegralOutside`, `g_v = u_v k_v` with `u_v ∈ N_n(F_v)`, `k_v ∈ GL_n(𝒪_v)`, and
  there `W_(o,v)(g_v) W'_(o,v)(g_v) = 1`, `Φ_v(e_n g_v) = 1` (since `e_n u_v = e_n` and
  `e_n k_v ∈ 𝒪_v^n`) and `|det g_v| = 1`. So `Ψ_(S∪∞)` is the global measure constant times
  the product of the local integrals at `S ∪ ∞`, times the volumes of
  `N_n(F_v) \ N_n(F_v) GL_n(𝒪_v)` for `v ∉ S`. The full integral is the same constant times
  the local integrals at `S ∪ ∞` times the local integrals `Ψ_v(s; W_o, W'_o, Φ_o)` at
  `v ∉ S`, and Theorem 3.3 gives each of them as `L(s, π_v × π'_v)` times the same local
  volume. Therefore the identity holds for every normalization of
  `whittakerQuotientMeasure`. The condition that `ψ_v` has conductor `𝒪_v` is the
  hypothesis of Theorem 3.3 that `ψ_v` is unramified.
* **The unramified computation.** For `v ∉ S` the proof needs
  `Ψ_v(s; W_o, W'_o, Φ_o) = L(s, π_v × π'_v)`: by the Iwasawa decomposition,
  `Φ_o(e_n a k) = 1_(𝒪_v)(a_n)` for diagonal `a`, and Shintani's formula and the Cauchy
  identity give the Euler factor (Jacquet–Shalika I, Proposition (2.3)). The Library does
  not state this equal-rank computation, so a proof must supply it.
* **Satake parameters.** As for `UnequalEulerFactorizationStatement`, the Library spectra
  are normalized by the spherical Hecke equations of
  `Langlands.Representation.Unramified.HeckeOperators` (Gross, *On the Satake
  isomorphism*, (3.14)). In that normalization the spectrum of the spherical constituent
  of the normalized principal series `i(χ_1, …, χ_n)` is `{χ_i(ϖ_v)}`, Cogdell's class
  `A_(π_v)`. So `partialEulerFactor` is the factor `det(I − q_v^(−s) A_(π_v) ⊗ A_(π'_v))^(−1)` of
  Theorem 3.3. The Library proves no comparison between Hecke spectra and principal
  series; a proof of this statement must supply it with the local computation.
* **Which spectra.** The presentation's spectra belong to the local components of a
  selected finite slice of `T`. Since `T` is irreducible, at `v ∉ S` they are the Satake
  parameters of the local component `π_v` of `T`. So the statement does not require `x` to
  lie in that slice.
* **Data that are not pure tensors.** `IsSphericalOutside` asks only that the cusp form of
  `x` be right invariant under `GL_n(𝒪_v)` for all finite `v ∉ S`. Since `T` is
  irreducible and `π_v` is unramified for `v ∉ S`, its spherical line is one-dimensional,
  so `x` is a finite sum of pure tensors with spherical components outside `S`; likewise
  `x'`. For `Φ`: `schwartzBruhat F n` is spanned by pure tensors `Φ_i`, and evaluating at
  the point with the same coordinates at `S ∪ ∞` and coordinates `0` at every finite
  `v ∉ S` shows that a `Φ` with `IsStandardOutside F n S Φ` equals
  `∑_i c_i Φ_(i,S∪∞) ⊗ ⊗_(v ∉ S) 1_(𝒪_v^n)` with constants `c_i = ∏_(v ∉ S) Φ_(i,v)(0)` (a
  finite product, since `Φ_(i,v) = 1_(𝒪_v^n)` for almost all `v`). Both sides of the
  identity are linear in `W`, `W'` and `Φ`, so the source's argument for decomposable
  data applies.
* **Uniform half-plane.** `σ` is chosen before `x`, `x'` and `Φ`. In the source, absolute
  convergence of `Ψ` for `Re s ≫ 0` comes from the gauge estimates for the Whittaker
  functions, whose exponents do not depend on the vectors, together with boundedness and
  rapid decay of `Φ`; neither gives a threshold that depends on `Φ` or on the vectors.
  The Euler product converges absolutely beyond a bound depending only on the spectra.
  `σ` may depend on `ψ`, `T`, `T'`, `P`, `P'` and `S`.
* **The places in `S` and at infinity.** Cogdell's `S` contains the archimedean places,
  while the Library's `S` is a set of finite places. So Cogdell's `∏_(v ∈ S) Ψ_v` is the
  integral `Ψ_(S∪∞)` of `PartialEqualWhittakerIntegral`.

## Deviations from the source

* `Ψ_(S∪∞)` is not a product of local integrals. It is the global integral over the
  classes whose components at `v ∉ S` lie in `N_n(F_v) GL_n(𝒪_v)`; see the Markdown of
  `PartialEqualWhittakerIntegral`.
* The contract allows assuming that the presentations have irreducible admissible finite
  components (`HasIrreducibleAdmissibleComponents`). The statement omits this hypothesis,
  so it is stronger. Only the places `v ∉ S` enter, and there the unramified data of a
  presentation already supply irreducibility, admissibility and the spectrum.
* The statement is the Euler factorization of the Whittaker integral `Ψ`. Combined with
  `EqualUnfoldingStatement` (`I = Ψ` on a right half-plane) it gives the source's
  factorization of `I(s; φ, φ', Φ)` on the common half-plane.

## Provenance

The statement transcribes Cogdell pp.210, 215 and 219 onto the Library's actual cuspidal
realizations, spectral presentations, Whittaker functions, Schwartz–Bruhat space and
quotient measures. The choices of form (the restricted integral `Ψ_(S∪∞)`, the order of
quantifiers, and the spherical and standard hypotheses on `x`, `x'` and `Φ`) are
internal and explained above.
