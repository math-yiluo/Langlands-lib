# Partial Euler factorization of the unequal-rank global Whittaker integral

`Langlands.Global.RankinSelbergGlobal.UnequalEulerFactorizationStatement` is the partial
Euler factorization, at the unramified places, of the global Rankin–Selberg Whittaker
integral `Ψ(s; W, W')` of a pair of cusp forms on `GL_n × GL_m` with `m < n`. It is a
Prop-valued statement. Nothing here proves it.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
*An Introduction to the Langlands Program* (2004), registered as
`cogdell-2004-analytic-theory-gln` (PDF SHA-256 `8117f145…`, PDF page = printed page + 3).

* §2.2, printed p.206 (PDF p.209): for factorizable cusp forms the Whittaker functions
  factor, `W_φ(g) = ∏_v W_(φ_v)(g_v)`, so the integral `Ψ(s; W_φ, W'_φ')` factors into local
  integrals. Using the unramified computation one gets
  `Ψ(s; W_φ, W'_φ') = (∏_(v ∈ S) Ψ_v(s; W_(φ_v), W'_(φ'_v))) · L^S(s, π × π')`.
* Theorem 3.3, printed p.215 (PDF p.218): if `π_v`, `π'_v` and `ψ_v` are unramified, and
  `W_o`, `W'_o` are the `GL(𝒪_v)`-fixed Whittaker functions with `W_o(e) = W'_o(e) = 1`, then
  `Ψ_v(s; W_o, W'_o) = L(s, π_v × π'_v) = det(I − q_v^(−s) A_(π_v) ⊗ A_(π'_v))^(−1)`. This uses
  `vol(GL_m(𝒪_v)) = 1`. Here `A_π` is the Satake (Langlands) class.
* §4.1, proof of Theorem 4.1, printed p.219 (PDF p.222): the same identity written with
  `L^S(s, π × π') = ∏_(v ∉ S) L(s, π_v × π'_v)`, which converges absolutely for `Re s ≫ 0`.

The local computation is due to Jacquet–Shalika (*Euler products II*, §1.4, registered as
`jacquet-shalika-1981-euler-ii`). The Library states it as
`Langlands.RankinSelberg.UnramifiedPairIntegralStatement` (module
`Langlands.Representation.RankinSelberg.UnramifiedPairStatement`).

## The statement

Let `F : Type u` be a number field with `[CompactSpace (AdeleQuotient F)]`. Let
`ψ : HarmonicAnalysis.UnitaryAdditiveCharacter (Adeles F)` be trivial on `F`. This type
consists of the continuous, circle-valued, nontrivial additive characters. So `ψ.complex`
satisfies the hypothesis `IsStandardAdditiveCharacter` used by the published unequal-rank
statements. Let `t < r`, so `m = t + 1 < n = r + 1`. Let `T` and `T'` be actual cuspidal
realizations of `GL_n` and `GL_m`, and let `P`, `P'` be spectral presentations of them
(universe `uQ` for the local factors). Let `S` be a finite set of finite places
containing `P.exceptional` and `P'.exceptional` and satisfying
`FunctionalEquationComparison.FiniteAdditiveSupport ψ S`: at every finite `v ∉ S` the
canonical local component of `ψ` exists and has conductor `𝒪_v` (additive conductor
`0`).

Then there exists `σ : ℝ` with the following property. Take any vectors `x : T.Space`,
`x' : T'.Space` with `IsSphericalOutside F T S x` and `IsSphericalOutside F T' S x'`, that
is, fixed by `GL(𝒪_v)` at every finite `v ∉ S`. Set
`W = cuspWhittaker F T ψ.complex x` and `W' = cuspWhittaker F T' ψ.complex⁻¹ x'`, the
global Whittaker functions of the cusp forms for the standard characters of `ψ` and
`ψ⁻¹` (module `Langlands.Global.RankinSelberg.UnequalIntegrals`). Then for every `s` with
`σ < Re s`:

1. `unequalWhittakerIntegrand F h W W' s` is integrable for `whittakerQuotientMeasure F m`.
   This is absolute convergence of `Ψ(s; W, W')`.
2. `∑_(v ∉ S) ‖L_v(s) − 1‖` converges, where
   `L_v(s) = partialEulerFactor P P' hP hP' v s`. This is absolute convergence of the Euler
   product.
3. There is `p` with `HasProd (fun v => L_v(s)) p` (the unconditional product over the
   finite places `v ∉ S`) and
   `unequalWhittakerIntegral F h W W' s = partialUnequalWhittakerIntegral F h S W W' s * p`.

Here `partialEulerFactor P P' hP hP' v s = ∏_(i,j) (1 − a_i b_j q_v^(−s))^(−1)` (module
`Langlands.Global.Factors.CuspidalPairBoundaryNonvanishingStatement`). The multisets `a`
and `b` are the spectra that the presentations `P` and `P'` supply at `v`.
`partialUnequalWhittakerIntegral` is `Ψ_(S∪∞)` from
`Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`. Every convergence claim is in
the conclusion, and no binder supplies an integral, its value or its convergence.

## Normalizations and comparison with the source

* **Spherical Whittaker functions.** The statement takes no local Whittaker functions.
  Its objects are global: the actual Whittaker functions `W`, `W'` of global vectors. So
  the normalization `W_o(e) = 1` of Theorem 3.3 enters only through the proof. Let `x` be
  a pure tensor whose components at `v ∉ S` are spherical. Then
  `W(g) = W_(S∪∞)(g_(S∪∞)) ∏_(v ∉ S) W_(o,v)(g_v)` with every `W_(o,v)(e) = 1`, and the
  scalar is absorbed into the factor at `S ∪ ∞`. On the set selected by
  `unipotentIntegralOutside`, `g_v = n_v k_v` with `n_v ∈ N_m(F_v)`, `k_v ∈ GL_m(𝒪_v)`. There
  `W_(o,v)(diag(g_v, I)) W'_(o,v)(g_v) = ψ_v(n_v) ψ_v(n_v)^(−1) = 1` and `|det g_v| = 1`. So
  `Ψ_(S∪∞)` is the global measure constant times the product of the local integrals at
  `S ∪ ∞`, times the local volumes of `N_m(F_v) \ N_m(F_v) GL_m(𝒪_v)` at `v ∉ S`. The full
  integral is the same constant times the local integrals at `S ∪ ∞` times the local
  integrals `Ψ_v` at `v ∉ S`. Theorem 3.3 gives each `Ψ_v`: it is `L(s, π_v × π'_v)` times the
  same local volume (which is `1` in Cogdell's normalization). Therefore the identity holds
  for every normalization of `whittakerQuotientMeasure`. No factorization of the global
  measure appears in the statement. The condition that `ψ_v` has conductor `𝒪_v` is the
  hypothesis of Theorem 3.3 that `ψ_v` is unramified.
* **Satake parameters.** The Library spectra are normalized by the spherical Hecke
  equations `T_i f = q_v^(i(n−i)/2) e_i(a) f` on the whole `GL_n(𝒪_v)`-fixed space
  (`Unramified.standardHeckeScalar`, module
  `Langlands.Representation.Unramified.HeckeOperators`). Here `T_i` is the characteristic
  function of `GL_n(𝒪_v) diag(ϖ I_i, I_(n−i)) GL_n(𝒪_v)` with `vol GL_n(𝒪_v) = 1`, and `e_i`
  is the `i`-th elementary symmetric function. This is the Satake normalization of Gross,
  *On the Satake isomorphism* (1998), (3.14), as recorded in that module's Markdown. In it
  the spectrum of the spherical constituent of the normalized principal series
  `i(χ_1, …, χ_n)` is `{χ_i(ϖ_v)}`, Cogdell's class `A_(π_v)`. So
  `partialEulerFactor` is exactly the factor `det(I − q_v^(−s) A_(π_v) ⊗ A_(π'_v))^(−1)` of
  Theorem 3.3. The Library proves no comparison between Hecke spectra and principal series
  (the Markdown of `HeckeOperators` lists it as an open obligation). A proof of this
  statement must supply that comparison together with the local computation.
* **Which spectra.** The presentation's spectra belong to the local components of a
  selected finite slice of `T`. Since `T` is irreducible, at `v ∉ S` they are the Satake
  parameters of the local component `π_v` of `T`. So the statement does not require `x` to
  lie in that slice.
* **Vectors that are not pure tensors.** `IsSphericalOutside` asks only that the cusp
  form of `x` be right invariant under `GL_n(𝒪_v)` for all finite `v ∉ S`. Since `T` is
  irreducible and `π_v` is unramified for `v ∉ S`, its spherical line is one-dimensional.
  So such an `x` is a finite sum of pure tensors with spherical components outside `S`.
  Both sides of the identity are linear in `W` and in `W'`, so the source's argument for
  factorizable vectors applies.
* **Uniform half-plane.** `σ` is chosen before the vectors. In the source, absolute
  convergence of `Ψ` for `Re s ≫ 0` comes from the gauge estimates (p.206). They bound the
  Whittaker function of each vector by a gauge whose exponent does not depend on the
  vector, so the threshold does not depend on the vectors either. The Euler product
  converges absolutely for `Re s` beyond a bound depending only on the spectra. The order
  of quantifiers keeps this uniformity. `σ` may depend on `ψ`, `P`, `P'` and `S`.
* **The places in `S` and at infinity.** Cogdell's `S` contains the archimedean places,
  while the Library's `S` is a set of finite places. So Cogdell's `∏_(v ∈ S) Ψ_v` is the
  integral `Ψ_(S∪∞)` of this file.

## Deviations from the source

* `Ψ_(S∪∞)` is not a product of local integrals. It is the global integral over the
  classes whose components at `v ∉ S` lie in `N_m(F_v) GL_m(𝒪_v)`. The reasons are given
  above and in the Markdown of `PartialWhittakerIntegrals`.
* The contract allows assuming that the presentations have irreducible admissible finite
  components (`HasIrreducibleAdmissibleComponents`). The statement omits this hypothesis,
  so it is stronger. Only the places `v ∉ S` enter, and there the unramified data of a
  presentation already supply irreducibility, admissibility and the spectrum.
* The statement is the Euler factorization for the Whittaker integral `Ψ`. Combined with
  `UnequalUnfoldingStatement` it gives the source's factorization of `I(s; φ, φ')` on the
  common half-plane.

## Provenance

The statement transcribes Cogdell pp.206, 215 and 219 onto the Library's actual cuspidal
realizations, spectral presentations, Whittaker functions and quotient measures. The
choices of form (the restricted integral `Ψ_(S∪∞)`, the order of quantifiers, and the
spherical hypothesis on vectors) are internal and explained above.
