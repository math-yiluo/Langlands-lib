# Ordinary absolute convergence of the two-block Jacquet integral

Author: Worker 814. Worker 484 specified the unit as a statement prerequisite
for the dominant-rank joint gamma/L task `d7ca9f6d`.

Source: H. Jacquet, I. I. Piatetskii-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), registered as
`jpss-1983-rankin-selberg` (SHA-256 `d9feed63…62245`). The assertion is in
Section (4.6), printed pages 410–411 (one-based PDF pages 45–46). The growth
input is Section (2.5), printed pages 388–389, and the scope is Section (2.1),
printed page 385. No errata note for this source is registered.

Module `Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
states the assertion as the proposition
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement`. It proves no
convergence. Its other declarations are a transparent family abbreviation and
small definitional bridges (listed at the end).

## The source assertion

On printed page 410 the source fixes `τ₁, τ₂` and writes `σ₁ = τ₁ ⊗ α^(-u)`,
`σ₂ = τ₂ ⊗ α^u`, with `α = |det|` and `u` "a positive real number sufficiently
large". It puts `σ_u = Ind(G_t, Q; σ₁ × σ₂)`, where `Q` is the lower standard
parabolic of type `(t₁, t₂)`, and realizes `σ_i` on `W(σ_i; ψ̄)`. A section
`f` of `σ_u` satisfies the covariance (4.6.1). The source then asserts: "if
`u ≫ 0`, the integral

```
(4.6.2)   ∫ f[(1 x; 0 1) g; e, e] θ[(1 x; 0 1)] dx
```

converges. It suffices to prove this for `g = e`."

On printed page 411 it writes `f = f₀ φ_u` with `f₀` in the `u`-independent
space `Ind(G_t, Q; τ₁, τ₂)`. Then it uses (2.5) to majorize
`|h(n̄a)| ≤ ξ(a)` for `h(g) = f₀(g; e, e)`, where `ξ` is a finite sum of
positive quasi-characters of `A_t`. This reduces the claim to the convergence
of a positive integral `∫ η̃[(1 x; 0 1)] dx` for `u ≫ 0`, which it calls "a
special case of a well-known result". The proof bounds the absolute value of
the integrand, so the convergence is absolute.

## The formal statement

```
∀ p [Fact p.Prime] (F : PadicField.{uF} p),
  letI := F.canonicalTopologicalData.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  ∀ ψ ν t m h {W} [..] τ,
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
    ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i), (∀ i, (ell i).val ≠ 0) →
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      ∀ f : TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u),
        TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val)
          (rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)) f
```

The binders are:

- `p` is a prime and `F : PadicField.{uF} p`. The topology is the canonical
  one, `F.canonicalTopologicalData.topology`, and the measurable space is its
  Borel σ-algebra.
- `ψ : UnitaryAdditiveCharacter F.Carrier` is any supplied character for that
  topology. The source's `ψ` is a fixed nontrivial character; no
  nontriviality or conductor hypothesis is imposed here, since the
  self-duality of `ν` (below) is with respect to this same `ψ`.
- `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` is
  any supplied self-dual Haar measure. The statement neither chooses one nor
  assumes that one exists. If none exists, the statement is vacuous for that
  `ψ`.
- `t : ℕ`, `m : Fin 2 → ℕ` and `h : ∑ i, (m i + 1) = t + 1`. Block `i` has
  rank `m i + 1`, so the source's `(t₁, t₂)` is `(m 0 + 1, m 1 + 1)` and its
  `G_t` is `GL_(t+1)`. Rank-one blocks (`m i = 0`) are included.
- `W : Fin 2 → Type uW` is an arbitrary dependent family of complex vector
  spaces, and `τ i` is any representation of `GL_(m i + 1)(F)` on `W i`. The
  field universe `uF` and the carrier universe `uW` are independent.
- The block hypotheses are exactly the published full standard
  `IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)` of
  `Langlands.Representation.RankinSelberg.AnalyticStatement`. This is the
  source's Whittaker type (2.1): admissibility, finite generation of
  `(τ i).asModule` over the actual group algebra
  `MonoidAlgebra ℂ (GL_(m i + 1)(F))`, and a linear equivalence of the space of
  standard functionals with `ℂ`. Irreducibility, genericity in the irreducible
  sense, unitarity and smoothness beyond admissibility are not assumed, so
  reducible blocks are included.
- `ell i : Whittaker.glInverseFunctionals ψ (m i) (τ i)` are supplied
  inverse-character functionals with `(ell i).val ≠ 0`.

The conclusion asserts one real bound `C`. It is chosen after all the data
above, so it may depend on `p`, `F`, `ψ`, `ν`, `t`, `m`, `h`, `W`, `τ` and
`ell`. It is chosen before `u`, the section `f` and the ambient element `g`
(which is quantified inside `IsAbsIntegrable`), so it is independent of all
three. This is the source's "for `u ≫ 0`" with the section and `g` arbitrary.
The source's restriction to positive `u` is not lost: a bound `C` can always be
replaced by `max C 0`.

## The opposite real twists

`twoBlockOppositeTwistBlocks F m τ u` is the transparent abbreviation

```
fun i => Langlands.twist
  (F.canonicalTopologicalData.determinantComplexPower (m i + 1)
    (if i = 0 then -(u : ℂ) else (u : ℂ)))
  (τ i)
```

It reuses the published `PadicField.TopologicalData.determinantComplexPower`
(`g ↦ |det g|^s` for the normalized absolute value, from
`Langlands.Representation.Shahidi.Induction`) and `Langlands.twist`. By
`twoBlockOppositeTwistBlocks_apply`, block `0` acts by
`|det g|^(-u) • τ 0 g` and block `1` by `|det g|^u • τ 1 g`. These are the
source's `σ₁ = τ₁ ⊗ α^(-u)` and `σ₂ = τ₂ ⊗ α^u`, on the same carriers `W i`.
At real `u` the complex power is the real power
(`determinantComplexPower_ofReal`).

This family is not the Section (4.5) deformation, which twists only the first
block by `+u` with complex `u`. It is also not the Shahidi half-parameter family
`shahidiTwistedPair`, which uses `|det|^(t/2)` and `|det|^(-t/2)`. Neither is
used.

## The actual lower induction

The sections are the published
`TwoBlockJacquet.Sections F h (twoBlockOppositeTwistBlocks F m τ u)` of
`Langlands.Representation.RankinSelberg.TwoBlockJacquetData`. This is the
carrier of the actual normalized induction
`F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
((succBlockShape m h).blockTensor σ)` from the lower block parabolic, with
`σ` the twisted blocks. This is the source's `σ_u`. No abstract section space or
induction certificate is used. The covariance (4.6.1) is the published
`TwoBlockJacquet.scalarSection_covariant`.

## The integrand, kernel and sign conventions

`TwoBlockJacquet.IsAbsIntegrable ψ ell μ f` means
`∀ g, Integrable (TwoBlockJacquet.integrand ψ ell f g) μ`. The integrand is

```
x ↦ tensorContraction ell (f(upperRadical h x * g)) * positiveKernel ψ x,
```

where `x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier`. Here
`upperRadical h x` is the matrix `(1 x; 0 1)` of `GL_(t+1)`, and
`tensorContraction ell` is the linear map `⊗ v_i ↦ ∏ ℓ_i(v_i)`. By
`TwoBlockJacquet.positiveKernel_apply`, `positiveKernel ψ x = ψ(x_(m 0, 0))`,
the positive `ψ` of the lower-left corner of the upper-right rectangle. This
equals the source's `θ[(1 x; 0 1)] = ψ(Σ_i u_(i,i+1))`
(`positiveKernel_eq_superdiagonal_upperRadical`), with the positive, not the
conjugate, character. The scalar evaluation uses the same linear maps
`(ell i).val` on the twisted carriers; it is not a new functional.

## Measures

The measure on the rectangle is the published
`Langlands.RankinSelberg.rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)`. It is
the nested finite `Measure.pi` of copies of the supplied scalar Haar measure
`ν.val.measure`, one per matrix entry. It is the source's additive Haar measure
`dx` on `M(t₁ × t₂)`. Changing `ν` rescales the measure by a positive finite
constant, so the assertion does not depend on the normalization. The
statement keeps the supplied self-dual measure because the consumer task uses
it. No other measure appears: the Iwasawa decomposition and the measures on
`N̄`, `A` and `K` belong to the source's proof, not to its assertion.

## Ordinary absolute integrability

The conclusion is Mathlib's `MeasureTheory.Integrable` of the complex integrand
at every ambient `g : GL_(t+1)(F)`: a.e.-strong measurability together with a
finite integral of the norm. This is ordinary absolute convergence of the
Bochner integral `TwoBlockJacquet.jacquetFunction`, which is what the
majorization on page 411 proves. The source's integrand is locally constant,
since sections are smooth, so measurability is implicit there. A stable
integral, a principal-value limit, or convergence of an exhausting sequence of
compact integrals would not suffice. The statement asserts integrability at
every `g` directly, not only at `g = e`. The source's reduction to `g = e`
(right translation preserves the section space; see
`TwoBlockJacquet.integrand_inducedRep`) is a proof step and is not assumed.

## From Whittaker models to supplied functionals

The source realizes each `σ_i` on its Whittaker model `W(σ_i; ψ̄)` and
evaluates `f(g)` at `(e, e)`. Here the carriers are arbitrary, and evaluation
at `e` is replaced by the supplied functionals `ell i`, which are equivariant
for the inverse standard character, the Library form of `ψ̄`.

The translation goes through coefficient images, not a model equivalence.
For a functional `ℓ`, the published `Whittaker.coefficientModel π ℓ` (in
`Langlands.Representation.Whittaker.Algebraic`) is the image of
`v ↦ (g ↦ ℓ(π g v))`. `Whittaker.modelMap π ℓ` is the intertwining map onto
it, and `Whittaker.modelMap_surjective` shows that every coefficient function
is `modelMap π ℓ v` for some `v`. Evaluating `modelMap π ℓ v` at `e` gives
`ℓ v`, so the source's evaluation of Whittaker functions at `e` is the scalar
evaluation `ℓ v` here. When `σ_i` is realized on `W(σ_i; ψ̄)` and `ℓ` is
evaluation at `e`, the two agree. The equivalence `Whittaker.modelEquiv`
requires irreducibility and is not used, so reducible blocks, whose
coefficient map may have a kernel, keep their actual carrier.

The supplied functionals are compatible with the twists:

- `determinantComplexPower_upperUnipotent` shows every determinant power is
  trivial on the upper unipotent subgroup, since unipotent matrices have
  determinant `1` (`unipotent_det`).
- `twoBlockOppositeTwistFunctional` is the published
  `Whittaker.twistFunctional` of `Langlands.Representation.Whittaker.AlgebraicTwist`.
  It shows that the same linear map `(ell i).val` is an inverse-character
  functional of the twisted block. `twoBlockOppositeTwistFunctional_val` says
  its underlying map is `(ell i).val`. So the statement's
  `fun i => (ell i).val` is the source's evaluation for `σ_i`, not only for
  `τ_i`.
- `twoBlockOppositeTwistBlocks_isOfWhittakerType_iff` applies the published
  `isOfWhittakerType_twist_iff` (from `WhittakerTypeTwist`, using
  `isOpen_ker_determinantComplexPower`). It shows that the twisted blocks have
  full Whittaker type for any character exactly when the `τ i` do. So every
  `σ_i` in the family has Whittaker type, as the source assumes.

The hypothesis uses the standard character, while the functionals use the
inverse character. These are compatible: the published
`isOfWhittakerType_standard_iff_inverse` (in `WhittakerGammaAdapters`) shows,
by the character change at `-1`, that full standard and full inverse-standard
Whittaker type are equivalent for the same representation. This matches the
source's remark in (2.1) that `ψ` may be replaced by `ψ̄`. No inverse type or
induced type is added as a hypothesis. Hence each `ell i` spans the
one-dimensional inverse functional space, and `(ell i).val ≠ 0` selects a
nonzero Whittaker functional. That hypothesis is included as the contract
specifies. It is harmless: for `ell i = 0` the integrand vanishes and the
conclusion holds trivially.

## Why the hypotheses support a uniform bound

The statement assumes no growth bound, finite exponent set, gauge, convergence
certificate or integrability of any section. The source derives uniformity
from the full Whittaker-type hypotheses as follows.

- (2.5), printed pages 388–389: for `π` generic, there is a finite set `X`
  of finite functions on `A_r`, "depending only on `π`", such that every
  `W ∈ W(π; ψ)` satisfies `W(a) = Σ_(χ ∈ X) φ_χ(α₁(a), …, α_(r-1)(a)) χ(a)`
  with Schwartz-Bruhat `φ_χ` (citing [J-P-S], Proposition (2.2)). Every finite
  function is dominated by a finite sum of quasi-characters. Page 411 applies
  this to the fixed blocks `τ_i` of Whittaker type (2.1), which may be
  reducible, and the statement keeps that full scope. Such expansions rest on
  the finite-dimensionality of Jacquet modules, which uses both admissibility
  and finite generation. This is why both conjuncts of `IsOfWhittakerType`
  matter, beyond the one-dimensional functional space.
- Page 411: `f = f₀ φ_u` is a bijection with the `u`-independent space
  `Ind(G_t, Q; τ₁, τ₂)`. A smooth `f₀` takes finitely many values on the
  maximal compact subgroup. So `|h(n̄a)| ≤ ξ(a)`, where the quasi-characters
  in `ξ` come from `X(τ₁)` and `X(τ₂)` alone; only the coefficients depend on
  `f₀`. The `u` dependence is the explicit factor `|det a₂ a₁⁻¹|^u`. The
  positive integral `∫ η̃` converges once `u` exceeds a threshold that depends
  only on the exponent of `η`.

So the threshold depends only on the `τ_i` (through finitely many exponents),
not on `f`. Since the section space is stable under right translation, the
same threshold also works at every `g`. This is the order `∃ C, ∀ u > C, ∀ f,
∀ g` of the formal statement. The statement only records this provenance and
does not formalize (2.5) or the "well-known result".

## Declarations

All are in namespace `Langlands.RankinSelberg`.

- `twoBlockOppositeTwistBlocks F m τ u` (abbrev): the opposite real twists
  above.
- `twoBlockOppositeTwistBlocks_apply`: block `i` acts by
  `|det g|^(∓u) • τ i g`, using `determinantComplexPower_apply`.
- `twoBlockOppositeTwistBlocks_zero`: at `u = 0` the family is `τ`, by
  `determinantComplexPower_zero` and `twist_one`.
- `determinantComplexPower_upperUnipotent`: `|det|^s` is `1` on
  `upperUnipotent n`.
- `twoBlockOppositeTwistBlocks_isOfWhittakerType_iff`: full Whittaker type of
  a twisted block, for any character `θ`, is equivalent to that of `τ i`.
- `twoBlockOppositeTwistFunctional` (def) and
  `twoBlockOppositeTwistFunctional_val` (simp, by `rfl`): the supplied
  inverse-character functional transported to the twisted block, with
  unchanged linear map.
- `TwoBlockJacquetConvergenceStatement` (def, `Prop`): the statement above.

These helper declarations are internal to this module and are not in the
source. They only make explicit what the source takes for granted when it
twists representations realized in Whittaker models.

## Not claimed

The module proves no convergence; `TwoBlockJacquetConvergenceStatement` is a
proposition for a later proof task. It contains no nonzero induced Whittaker
functional, Whittaker equivariance of the Jacquet integral,
coefficient-image spanning, quotient unfolding, functional equation, analytic
deformation or multiplicativity claim. It does not state the source's claim
that the resulting function lies in `W(σ_u; ψ̄)`, or that all elements of
`W(σ_u; ψ̄)` arise this way. It asserts nothing about the Section (4.5)
deformation, stable integrals or complex parameters.
