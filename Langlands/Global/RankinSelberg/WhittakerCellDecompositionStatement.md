# One-place Iwasawa cell decomposition of the Whittaker quotient measure

`Langlands.Global.RankinSelbergGlobal.WhittakerCellDecompositionStatement` says that the
partial integrals over `N_m(𝔸) \ GL_m(𝔸)` can be refined one finite place at a time.
Dropping the condition at one place `v ∉ S` turns the integral into a sum over the
Iwasawa cells `N_m(F_v) ϖ^λ GL_m(𝒪_v)`, `λ ∈ ℤ^m`, weighted by `δ_B(ϖ^λ)⁻¹`. It is a
Prop-valued statement. Nothing here proves it.

The module defines two helpers, `localPoint` and `modulusExponent`, and reuses
`unipotentIntegralClasses` from `PartialIntegralExhaustion`.

## Source and provenance

* J. W. Cogdell, *Lectures on L-functions, converse theorems, and functoriality for
  GL_n*, Fields Institute lectures (2003), registered as
  `cogdell-2003-fields-lectures-www`. Lecture 7, §3 "Calculating the integral", printed
  p.57 (0-based PDF page index 60). For the local unramified integral over
  `N_m(k) \ GL_m(k)`, the source writes: "Use the Iwasawa decomposition to write
  `GL_m = N_m A_m K_m` so that `h = n ϖ^J k` and `dh = dn δ_(B_m)^(−1)(ϖ^J) dk`." The
  integral then becomes a sum over `J ∈ ℤ^m` of the integrand at `ϖ^J` with weight
  `δ_(B_m)^(−1)(ϖ^J)`.
* J. W. Cogdell, *Analytic theory of L-functions for GL_n*, in Bernstein–Gelbart (eds.),
  *An Introduction to the Langlands Program* (2004), registered as
  `cogdell-2004-analytic-theory-gln` (PDF page = printed page + 3). §4.1, proof of
  Theorem 4.1, printed p.220 (PDF p.223): the global integrals factor as the product of
  the local integrals over `v ∈ S` times the partial L-function. At the places outside
  `S` the unramified computation, Theorem 3.3, printed p.215 (PDF p.218), is used.
  That computation is the one in the first source.

**Provenance of the formulation (internal).** Neither source states a global one-place
form. This statement is a formulation made for the Library. It is the local cell formula
of the first source at the single place `v`, transported to the adelic quotient
`N_m(𝔸) \ GL_m(𝔸)` with the other components of the class untouched. It is normalized so
that no volume of `GL_m(𝒪_v)` appears: the cell of `λ` is compared with the classes
`N_m(F_v) GL_m(𝒪_v)` at `v`, not with a point. This is the form needed by the
proof of `UnequalEulerFactorizationStatement` and the proof of
`EqualEulerFactorizationStatement`. The dual-side proof of
`UnequalDualEulerFactorizationStatement` also needs it. Each of them applies
the statement once for every place outside `S` and passes to the limit over `S`.

## Definitions

* `localPoint F m v h`, written `ι_v(h)`: the actual adelic point of `GL_m` whose
  component at the finite place `v` is `h ∈ GL_m(F_v)`. Its components at every other
  finite place and at the infinite places are the identity matrix. It is
  `(GeneralLinearGroupPoints.adelicEquiv F m).symm` applied to
  `AdelicGL.ofFinite F m (FiniteAdelicGL.localInclusion F m v h)`.
* `unipotentIntegralClasses F m S`, written `U_S`: the classes `q ∈ N_m(𝔸) \ GL_m(𝔸)`
  with `q.out ∈ unipotentIntegralOutside F m S`, that is, `g_w ∈ N_m(F_w) GL_m(𝒪_w)` at
  every finite place `w ∉ S` for the chosen representative `g = q.out`. This is the same
  set as the domain of `partialUnequalWhittakerIntegral` and
  `partialDualWhittakerIntegral` (module
  `Langlands.Global.RankinSelberg.PartialWhittakerIntegrals`). The condition
  `IsUnipotentIntegral` is stable under left multiplication by `N_m(F_w)`, so the set
  does not depend on the choice of representative.
* `modulusExponent λ = ∑_(i<j) (λ_i − λ_j)` for `λ : Fin m → ℤ`. Let `δ_B` be the
  modulus character of the upper triangular Borel subgroup of `GL_m(F_v)`, with
  `δ_B(diag(t_1, …, t_m)) = ∏_(i<j) |t_i / t_j|_v`. Let `ϖ` be a uniformizer, so
  `|ϖ|_v = q_v^(−1)` where `q_v = N(v)`. Then `δ_B(ϖ^λ)⁻¹ = q_v^(modulusExponent λ)`.

## The statement

Let `F` be a number field, `m : ℕ`, `S` a finite set of finite places, and `v` a finite
place with `v ∉ S`. Let `ϖ ∈ F_v^×` satisfy
`GeneralLinear.Iwasawa.IsUniformizingElement Valued.v ϖ`: `v(ϖ) < 1` and every nonzero
valuation is a power of `v(ϖ)`. Let `f : N_m(𝔸) \ GL_m(𝔸) → ℂ` be integrable for
`whittakerQuotientMeasure F m`. For `λ : Fin m → ℤ` let `ϖ^λ = GeneralLinear.Iwasawa.torus
ϖ λ = diag(ϖ^(λ_1), …, ϖ^(λ_m))`, and define the translate

`f_λ(q) = f(N_m(𝔸) · ι_v(ϖ^λ) · q.out)`.

This is left translation by `ι_v(ϖ^λ)` on the quotient. It is well defined because
`ι_v(ϖ^λ)` normalizes `N_m(𝔸)`. Then:

1. for every `λ`, `f_λ` is integrable on `U_S`;
2. `HasSum (fun λ => (N(v) : ℂ)^(modulusExponent λ) · ∫_(U_S) f_λ) (∫_(U_(S ∪ {v})) f)`.
   Here `N(v) = Ideal.absNorm v.asIdeal`, both integrals are for
   `whittakerQuotientMeasure F m`, and `HasSum` is unconditional summation over `ℤ^m`.

So `∫_(U_(S∪{v})) f = ∑_(λ ∈ ℤ^m) δ_B(ϖ^λ)⁻¹ ∫_(U_S) f_λ`.

## Why it holds (sketch)

* The Iwasawa decomposition `GL_m(F_v) = ⊔_λ N_m(F_v) ϖ^λ GL_m(𝒪_v)`, with `λ` unique,
  splits `U_(S∪{v})` into the disjoint cells
  `C_λ = U_(S∪{v}) ∩ {g_v ∈ N_m(F_v) ϖ^λ GL_m(𝒪_v)}`. In the Library these are
  `GeneralLinear.Iwasawa.exists_iwasawa` and `iwasawa_exponent_unique`. Then
  `∫_(U_(S∪{v})) f = ∑_λ ∫_(C_λ) f`.
* Left translation `L_λ` by `ι_v(ϖ^λ)` maps `U_S` bijectively onto `C_λ`, because
  `ϖ^λ N_m(F_v) GL_m(𝒪_v) = N_m(F_v) ϖ^λ GL_m(𝒪_v)`.
* `whittakerQuotientMeasure` is right `GL_m(𝔸)`-invariant and `L_λ` commutes with right
  translations. So `L_λ` pushes the measure forward to a constant multiple of itself,
  and the constant is `δ_B(ϖ^λ)`. This is the global form of the source's
  `dh = dn δ_B^(−1)(ϖ^J) dk`. Hence `∫_(U_S) f_λ = δ_B(ϖ^λ) ∫_(C_λ) f`.

## Normalizations and conventions

* The weight is `δ_B(ϖ^λ)⁻¹ = q_v^(∑_(i<j)(λ_i − λ_j))`, as in the source's
  `δ_(B_m)^(−1)(ϖ^J)`. For dominant `λ` (`λ_1 ≥ … ≥ λ_m`) it is at least `1`.
* `whittakerQuotientMeasure F m` is the Library quotient measure on `N_m(𝔸) \ GL_m(𝔸)`
  (module `Langlands.Global.RankinSelberg.WhittakerIntegrals`). It is the pushforward of
  the quotient Haar measure on `N_m(F) \ GL_m(𝔸)`, so `N_m(F) \ N_m(𝔸)` gets mass one.
  The identity is homogeneous in the measure, so its normalization does not matter.
* `f` is required to be integrable on the whole quotient. This is the hypothesis the
  proofs that use the statement need.
* The statement is universe-polymorphic in the number field `F : Type u`, like the
  other global Rankin–Selberg statements.
