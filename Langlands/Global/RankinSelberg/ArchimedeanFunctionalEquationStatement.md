# The archimedean Rankin–Selberg functional equation at one place

Module `Langlands.Global.RankinSelberg.ArchimedeanFunctionalEquationStatement`, namespace
`Langlands.Global.RankinSelbergGlobal`. It states result 1 of `ArchimedeanSemilocalTheoryStatement`: Jacquet 2009,
Theorem 2.1 (i)–(iii), for the archimedean restrictions of global Whittaker functions of
actual cuspidal realizations. Complex places and real places are separate declarations.

## Statements

All declarations are `Prop`-valued, in the number-field universe `u`.

* `ComplexUnequalFunctionalEquationStatement`: complex place, `t < r`.
* `ComplexEqualFunctionalEquationStatement`: complex place, equal ranks.
* `RealUnequalFunctionalEquationStatement`: real place, `t < r`.
* `RealEqualFunctionalEquationStatement`: real place, equal ranks.
* `ComplexPlaceFunctionalEquationStatement = ComplexUnequal… ∧ ComplexEqual…`.
* `RealPlaceFunctionalEquationStatement = RealUnequal… ∧ RealEqual…`.
* `ArchimedeanFunctionalEquationStatement = ComplexPlace… ∧ RealPlace…`, result 1 at all
  infinite places.

### `ComplexUnequalFunctionalEquationStatement`

The binders are those of the targets `UnequalSemilocalEquationStatement` and
`UnequalSemilocalFactorizationStatement`, restricted to one complex place:

* a number field `F` with `AdeleQuotient F` compact, and a unitary additive character `ψ` of
  `𝔸_F` trivial on `F`;
* `t < r` (so `n = r + 1 > m = t + 1`), actual cuspidal realizations `T`, `Td` of
  `GL_(r+1)` and `T'`, `Td'` of `GL_(t+1)`, with `Td` contragredient to `T` and `Td'` to `T'`
  (`IsContragredientOf`);
* a complex place `w` and `a ∈ ℂ^×` with `IsComplexAdditiveComponent ψ w a`: the
  component of `ψ` at `w` is `ψ_w = complexScaledCharacter a : z ↦ exp(2πi Tr(a z))`;
* lists `d`, `d'`, `dd`, `dd'` of `ComplexCharacterData` with `HasComplexPlaceParameter` at
  `w` for `T`, `T'`, `Td`, `Td'` respectively, given as hypotheses as in the targets;
* any quotient measure data `D : ComplexQuotientMeasureData t` on `N_m(ℂ) \ GL_m(ℂ)`;
* any `W : GL_n(ℂ) → ℂ` and `W' : GL_m(ℂ) → ℂ` with `IsComplexPlaceWhittaker F T ψ w W` and
  `IsComplexPlaceWhittaker F T' ψ⁻¹ w W'`: archimedean restrictions at `w` of global
  Whittaker functions `cuspWhittaker` of `T` for `ψ` and of `T'` for `ψ⁻¹`.

The conclusion: there are `σ ∈ ℝ` and `M, Md : ℂ → ℂ` such that

1. for `σ < Re s`, the integrand of `Ψ(s; W, W')` is integrable for `D.measure`, and the
   kernel of `Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')` is integrable for the product of `D.measure`
   and the rectangular measure self-dual for `ψ_w` (`complexUnequalDualMeasure`);
2. `s ↦ Ψ(s; W, W')` and `s ↦ Ψ_(n−m−1)(s; ρ(w_(n,m)) W̃, W̃')` are holomorphic
   (`DifferentiableOn ℂ`) on `{σ < Re s}`;
3. `M` and `Md` are meromorphic on `ℂ`, and on `{σ < Re s}` they equal the two integrals;
4. off a discrete set (`Filter.codiscrete ℂ`),
   `L_w(s) Md(1 − s) = ω'_w(−1)^r ε_w(s) L∨_w(1 − s) M(s)`.

In 4:

* `L_w(s) = ((complexPairLFactor d d').denominator s)⁻¹` and
  `L∨_w(s) = ((complexPairLFactor dd dd').denominator s)⁻¹`;
* `ε_w(s) = complexPairEpsilon d d' a |a| s`, with the normalization of the targets (the
  additive character `complexScaledCharacter a` and the self-dual measure
  `complexScaledMeasure |a|`);
* `ω'_w(−1) = complexMinusOneScalar T' w`, the defined scalar by which `−1 ∈ U(t+1)` acts
  at `w` (module `ArchimedeanPlaces`).

The integrals at `1 − s` lie in general outside the half-plane of convergence, so the
equation is stated for the continuations `M`, `Md`. It is Jacquet's
`Ψ_(n−m−1)(1 − s; ρ(w_(n,m)) W̃, W̃') / L∨(1 − s) = ω'(−1)^(n−1) ε(s) Ψ(s; W, W') / L(s)`
multiplied by `L(s) L∨(1 − s)`, with both integrals replaced by their continuations.

### `ComplexEqualFunctionalEquationStatement`

The same, with `T`, `Td`, `T'`, `Td'` all of rank `r + 1`, `D : ComplexQuotientMeasureData r`,
and also any Schwartz function `Φ : SchwartzMap (Fin (r+1) → ℂ) ℂ`. The two integrals are
`Ψ(s; W, W', Φ)` (`complexEqualIntegral`) and `Ψ(s; W̃, W̃', Φ̂)`
(`complexEqualDualIntegral`), with `Φ̂ = complexFourierTransform a Φ`, the Fourier transform
for `ψ_w` and its self-dual measure. Integrability of both integrands is for `D.measure`.
The equation is the same, with sign `ω'_w(−1)^r`. This includes `r = 0`, Tate's case
`GL_1 × GL_1` with trivial `N_1`.

### Real places

`RealUnequalFunctionalEquationStatement` and `RealEqualFunctionalEquationStatement` are the
same at a real place `v`, with `a ∈ ℝ^×` and `IsRealAdditiveComponent ψ v a`
(`ψ_v = realScaledCharacter a : x ↦ exp(2πi a x)`), `RealBlock` parameters with
`HasRealPlaceParameter`, `IsRealPlaceWhittaker`, `RealQuotientMeasureData`, the real
integrals of `ArchimedeanIntegrals`, Schwartz functions on `ℝ^(r+1)`, `realPairLFactor`,
`ε_v(s) = realPairEpsilon d d' a |a|^(1/2) s` and the sign
`ω'_v(−1)^r = realMinusOneScalar T' v ^ r`.

## Normalizations

* **Absolute values.** `|x|` at a real place, `|z|²` at a complex place (the normalized
  absolute value), in `|det g|^s`.
* **Additive character.** `ψ_v` is the component of `ψ` at `v`, i.e. the given `a`.
  `W` is a Whittaker function for `ψ_v`, `W'` for `ψ_v⁻¹ = ψ̄_v`.
* **Measures.** The inner variable of the dual block integral and the Fourier transform use
  the measure self-dual for `ψ_v`: `|a|^(1/2) dx` on `ℝ`, `|a| · 2 dx dy` on `ℂ`. The measure
  on `N \ GL` is any compatible quotient measure `D`, the same for the integral and its dual.
  Both sides of the equation are linear in `D.measure`, and any two such measures are
  proportional, so the choice does not matter.
* **Fourier transform.** `Φ̂(x) = ∫ Φ(y) ψ_v(∑_j y_j x_j) dy`, positive sign, as in the
  Library's global `fourierTransform`.
* **`w_n`, duals.** `W̃(g) = W(w_n ᵗg⁻¹)` with `w_n = GeneralLinear.weylLong`, as in the global
  `dualFunction`. `ρ(w_(n,m))` is right translation by `diag(1_m, w_(n−m))`, as in the global
  `unfoldingWeyl`.
* **`L` and `ε`.** The Library's archimedean pair factors of the parameters, with `ε` for
  `ψ_v` (the given `a`) and its self-dual measure. These are the standard (Tate)
  normalizations, in which `ε(s, sgn, x ↦ e^(2πix)) = i`. They are the expressions whose
  products over the infinite places are the targets' `L_∞`, `L∨_∞` and `ε_∞`.
* **Central sign.** `ω'_v(−1)^r = ω'_v(−1)^(n−1)` in both rank cases, with `ω'_v(−1)` the
  defined scalar of `−1` on `T'` at `v`.

## The central sign in the Library's conventions

Cogdell (Theorem 3.6, p.217) gives `ω'_v(−1)^(n−1)` in both rank cases. Jacquet (p.6) gives
`ω_π(−1)^(n′) ω_π′(−1)` for `n > n′` and `ω_π(−1)^(n−1)` for `n = n′`, in his conventions:

* **His `ε`.** Jacquet's Tate functional equation (p.5) uses his Fourier transform
  `∫ Φ(y) ψ(−xy) dy`, so his `ε(s, τ, ψ)` is the standard `ε(s, τ, ψ̄)`, which is
  `det τ(−1) ε(s, τ, ψ)`. For `τ = σ ⊗ σ′` of dimensions `n`, `n′`,
  `det τ(−1) = ω_π(−1)^(n′) ω_π′(−1)^n`.
* **Unequal ranks.** Converting to the standard `ε`, his sign becomes
  `ω_π(−1)^(n′) ω_π′(−1) · ω_π(−1)^(n′) ω_π′(−1)^n = ω_π′(−1)^(n+1) = ω_π′(−1)^(n−1)`, since
  `ω(−1)² = 1`.
* **Equal ranks.** His dual integral uses his Fourier transform `Φ̂_J(x) = Φ̂(−x)`. Since
  `Φ̂_J(e_n g) = Φ̂(e_n(−g))`, the substitution `g ↦ −g` gives
  `Ψ(s; W̃, W̃', Φ̂_J) = ω_π(−1) ω_π′(−1) Ψ(s; W̃, W̃', Φ̂)`, because
  `W̃(−g) = ω_π(−1) W̃(g)`, `W̃'(−g) = ω_π′(−1) W̃'(g)` and `|det(−g)| = |det g|`. With the
  conversion of `ε`, his sign becomes
  `ω_π(−1)ω_π′(−1) · ω_π(−1)^(n−1) · ω_π(−1)^n ω_π′(−1)^n = ω_π′(−1)^(n−1)`.

Both give `ω'_v(−1)^(n−1) = ω'_v(−1)^r`, Cogdell's sign. It is the sign stated here, and the
sign that the targets' sign clauses need (see the Markdown of
`ArchimedeanSemilocalTheoryStatement`).

## Why the functions are in Jacquet's Whittaker models

`IsComplexPlaceWhittaker F T ψ w W` says `W(g) = W_x(ι_w(g) a)` for some `x ∈ T.Space` and a
finite adelic point `a`, with `W_x = cuspWhittaker F T ψ x`.

* **Whittaker property.** `W_x(u h) = ψ(u) W_x(h)` for `u ∈ N(𝔸)`. For `u ∈ N(F_w)` at `w`,
  `ψ(ι_w(u)) = ψ_w(u)`, so `W(u g) = ψ_w(u) W(g)`: `W` is a Whittaker function for `ψ_w`.
* **The model.** The map `x ↦ W_x(ι_w(·) a)` commutes with right translation by `GL_n(F_w)`.
  The archimedean component `π_w` of `T` at `w` is irreducible and generic (a local component
  of a cuspidal representation). The global representation is the tensor product of its
  local components, so the image of `x` is a finite sum of Whittaker functions of `π_w`, i.e.
  `W` lies in the Whittaker model `W(π_w : ψ_w)`.
* **The parameter.** `HasComplexPlaceParameter T w d` embeds the `K`-finite standard module
  of `d` into `T` at `w`. Since `π_w` is irreducible, `π_w` is that standard module, and `d`
  is its Langlands parameter. A generic irreducible representation is its own standard
  module, so `W(π_w : ψ_w)` is Jacquet's `W(π_(σ,u) : ψ_w)` (p.4) for the parameter `d`.
  This uses that the Library's correspondence between blocks and standard modules is the
  Langlands classification in Jacquet–Shalika's normalization; the targets rest on the same
  identification (paragraph "Archimedean conventions" of the Markdown of
  `UnequalSemilocalEquationStatement`).
* `W'` is the same for `T'` and `ψ_w⁻¹`, giving Jacquet's model for `ψ̄`.

The real places are the same.

## Products over the infinite places

For data at every infinite place, as in the targets, the product over the real and complex
places of `L_v(s)`, `L∨_v(s)` and `ε_v(s)` is exactly the targets' `infiniteL s`,
`dualInfiniteL s` and `infiniteEpsilon s`: the same `(denominator s)⁻¹` and the same
`realPairEpsilon (dR v) (dR' v) (aR v) √|aR v|` and `complexPairEpsilon (dC v) (dC' v) (aC v) |aC v|`.
The product of the equations of result 1 is therefore the targets' identity with the sign
`∏_(v | ∞) ω'_v(−1)^r`. The data produced by `ArchimedeanFactorizationStatement` satisfy the
hypotheses of these statements.

## Choices of form

* **Per place.** The statements are for one place, with the archimedean integrals over `ℝ` or
  `ℂ`, so that the complex part can be used alone over a totally complex field.
* **Universal data.** Every quotient measure, every pair of restrictions and every Schwartz
  function is covered. `σ`, `M`, `Md` depend on them.
* **Holomorphy.** Clause 2 states holomorphy on the half-plane, which the consumers use to
  show that the products of the continuations do not vanish identically (an analytic point
  with nonzero value).
* **Continuation in multiplied-out form.** Meromorphy on `ℂ` and the equation off a discrete
  set are stated for `M`, `Md`. Jacquet's further assertions (holomorphic multiples of `L`,
  boundedness in vertical strips) are not stated.

## Sources

* H. Jacquet, *Archimedean Rankin–Selberg integrals* (2009),
  `jacquet-2009-archimedean-rankin-selberg` (PDF page = printed page): p.3 (Fourier transform
  `∫ Φ(Y) ψ(−Tr(ᵗX Y)) dY`, self-dual measure), p.4 (Whittaker models `W(π_(σ,u) : ψ)`, `W̃`),
  p.5 (`γ`, the Tate functional equation), p.6 (integrals (2.4)–(2.6), Theorem 2.1 with the
  signs `ω_π(−1)^(n′) ω_π′(−1)` and `ω_π(−1)^(n−1)`).
* J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004),
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3), Theorems 3.5–3.6,
  pp.216–217 (sign `ω'(−1)^(n−1)` in both rank cases).

## Provenance

Source statement: Jacquet 2009, Theorem 2.1 (i)–(iii), and Cogdell 2004, Theorem 3.6, in the
Library's conventions, for the Whittaker functions described above. The conversion of the
sign is derived above.
