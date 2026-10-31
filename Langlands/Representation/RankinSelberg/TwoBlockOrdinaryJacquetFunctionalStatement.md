# The ordinary two-block Jacquet integral as a nonzero Whittaker functional

Author: Worker 886. Worker 484 specified the unit as a statement prerequisite
for the dominant-rank joint gamma/L task `d7ca9f6d`.

Source: H. Jacquet, I. I. Piatetskii-Shapiro, J. A. Shalika, *Rankin-Selberg
convolutions*, Amer. J. Math. 105 (1983), registered as
`jpss-1983-rankin-selberg` (SHA-256 `d9feed63…62245`). The integral and the
model assertion are in Section (4.6), printed pages 410–411 (one-based PDF
pages 45–46). Whittaker type and the coefficient spaces `W(π; ψ)` are in
Section (2.1), printed pages 385–386 (one-based PDF pages 20–21). No errata
note for this source is registered.

Module
`Langlands.Representation.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement`
contains one declaration, the proposition
`Langlands.RankinSelberg.TwoBlockOrdinaryJacquetFunctionalStatement.{uF,uW}`.
It proves nothing. It imports only
`Langlands.Representation.RankinSelberg.TwoBlockJacquetConvergenceStatement`
and reuses the published definitions listed below; it introduces no section
space, kernel, integral, induced representation or functional notion.

## The source assertion

On printed page 410 the source writes `σ₁ = τ₁ ⊗ α^(-u)`, `σ₂ = τ₂ ⊗ α^u`
with `α = |det|` and `u` a sufficiently large positive real, and puts
`σ_u = Ind(G_t, Q; σ₁ × σ₂)` for the lower standard parabolic `Q` of type
`(t₁, t₂)`. It realizes `σ_i` on `W(σ_i; ψ̄)`, so a section `f` has values
`f(g; h₁, h₂)`, with covariance (4.6.1). It then proves that the integral

```
(4.6.2)   ∫ f[(1 x; 0 1) g; e, e] θ[(1 x; 0 1)] dx
```

converges for `u ≫ 0`. On printed page 411, after the convergence argument,
it states: "the function `W'` of `g` defined by (2) evidently belongs to
`W(σ_u; ψ̄)`. Moreover, all elements of `W(σ_u; ψ̄)` are of this form."

By (2.1)(3), `W(σ_u; ψ̄)` is the space of functions `g ↦ λ(σ_u(g) v)` for a
fixed functional `λ` in the one-dimensional space of `ψ̄`-functionals of
`σ_u`. The model assertion therefore has two parts:

1. **Realization.** The map `f ↦ (g ↦ (4.6.2))` is given by a nonzero
   `ψ̄`-Whittaker functional of `σ_u`: there is a nonzero `J` with
   `(4.6.2) = J(σ_u(g) f)`. Then the integral functions are exactly the
   coefficient functions of `J`, that is, the coefficient image of `J`.
2. **Comparison.** That coefficient image is `W(σ_u; ψ̄)`, the coefficient
   image of an arbitrary nonzero functional of `σ_u`. This uses that `σ_u`
   itself has Whittaker type, so that its nonzero functionals are
   proportional.

## What this proposition states

This proposition is part 1 only. It realizes the entire family of ordinary
integral functions as the coefficients of one nonzero functional `J` of its
own. It does not identify the coefficient image of `J` with the image of any
other nonzero functional of the induced representation. That comparison
needs uniqueness of the induced functional, or full Whittaker type of the
induced representation, and is separately owned. In particular the
proposition claims no equivalence of `σ_u` with a Whittaker model, which
would be false in general for reducible carriers, whose coefficient maps may
have kernels.

This focused formulation is an internal extraction: it is the integral
realization used in Section (4.6), separated from the comparison part of the
source's sentence. The source does not state it as a separate result.

## The formal statement

```
∀ p [Fact p.Prime] (F : PadicField.{uF} p),
  letI := F.canonicalTopologicalData.topology
  letI : MeasurableSpace F.Carrier := borel F.Carrier
  ∀ ψ ν t m h {W} [..] τ,
    (∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)) →
    ∀ ell : ∀ i, glInverseFunctionals ψ (m i) (τ i), (∀ i, (ell i).val ≠ 0) →
    ∃ C : ℝ, ∀ u : ℝ, C < u →
      (∀ f : Sections F h τ_u, IsAbsIntegrable ψ (fun i => (ell i).val) μ f) ∧
      ∃ J : glInverseFunctionals ψ t (inducedRep F h τ_u),
        J.val ≠ 0 ∧
        ∀ f g, J.val (inducedRep F h τ_u g f) =
          jacquetFunction ψ (fun i => (ell i).val) μ f g
```

Here `τ_u = twoBlockOppositeTwistBlocks F m τ u`,
`μ = rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)`, and `Sections`,
`inducedRep`, `IsAbsIntegrable` and `jacquetFunction` are in namespace
`Langlands.RankinSelberg.TwoBlockJacquet`. The Lean source spells out each
abbreviation in full.

### Binders

These are the binders of the published
`Langlands.RankinSelberg.TwoBlockJacquetConvergenceStatement`, in the same
order and with the same meaning.

- `p` is a prime and `F : PadicField.{uF} p`, with the canonical topology
  `F.canonicalTopologicalData.topology` and its Borel σ-algebra.
- `ψ : UnitaryAdditiveCharacter F.Carrier` is any supplied character for that
  topology. The structure bundles continuity, unit-circle values and
  nontriviality.
- `ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ` is
  any supplied self-dual Haar measure. No such measure is chosen and its
  existence is not assumed; if none exists the statement is vacuous for `ψ`.
- `t : ℕ`, `m : Fin 2 → ℕ`, `h : ∑ i, (m i + 1) = t + 1`. Block `i` has rank
  `m i + 1`, so the source's `(t₁, t₂)` is `(m 0 + 1, m 1 + 1)` and `G_t` is
  `GL_(t+1)`. Rank-one blocks `m i = 0` are included.
- `W : Fin 2 → Type uW` is an arbitrary dependent family of complex vector
  spaces and `τ i` an arbitrary representation of `GL_(m i + 1)(F)` on
  `W i`. The universes `uF` and `uW` are independent.
- The block hypotheses are exactly the full standard
  `IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i)` of
  `Langlands.Representation.RankinSelberg.AnalyticStatement`: admissibility,
  finite generation over the group algebra, and a linear equivalence of the
  standard functional space with `ℂ`. This is the source's Whittaker type
  (2.1). Irreducibility is not assumed, so reducible blocks are included.
- `ell i : Whittaker.glInverseFunctionals ψ (m i) (τ i)` are supplied
  inverse-character functionals with `(ell i).val ≠ 0`.

### Conclusion and quantifier order

There is one real bound `C`, chosen after all the data above and before `u`,
the sections and the ambient elements. It may depend on `p`, `F`, `ψ`, `ν`,
`t`, `m`, `h`, `W`, `τ` and `ell`, but not on `u`, `f` or `g`. For every real
`u > C` both clauses hold:

1. Every section `f` of the actual induction of `τ_u` satisfies
   `TwoBlockJacquet.IsAbsIntegrable ψ (fun i => (ell i).val) μ f`: the raw
   integrand of (4.6.2) is Mathlib-`Integrable` for `μ` at every ambient
   element `g`. This is the same clause as the conclusion of
   `TwoBlockJacquetConvergenceStatement`, with the same bound.
2. There is a functional
   `J : Whittaker.glInverseFunctionals ψ t (TwoBlockJacquet.inducedRep F h τ_u)`
   with `J.val ≠ 0`, such that for every section `f` and every
   `g : GL_(t+1)(F)`,
   `J.val (inducedRep F h τ_u g f) = jacquetFunction ψ (fun i => (ell i).val) μ f g`.
   `J` may depend on `u` and the preceding data, and is chosen before `f`
   and `g`.

Membership in `glInverseFunctionals ψ t` is the actual equivariance
`J(σ_u(n) f) = ψ̄(n) J(f)` for all `n` in the upper unipotent subgroup of
`GL_(t+1)(F)`, with `ψ̄ = inverseStandardCharacter ψ t`, the Library form of
the source's `ψ̄`. Together with `J.val ≠ 0` this makes `J` a nonzero
Whittaker functional of `σ_u` for `ψ̄`. The identity says that the integral
function of `f` is the coefficient `g ↦ J(σ_u(g) f)`, the element of the
coefficient image `Whittaker.coefficientModel` of `J` given by `f`. At
`g = 1` it gives `J(f) = jacquetFunction … f 1`, so `J` is uniquely
determined by the identity, and the identity at every `g` says that this
functional's coefficients are the integrals.

Since the first clause gives integrability, `jacquetFunction` here is an
absolutely convergent Bochner integral, not the zero value that Mathlib
assigns to non-integrable functions.

## The objects used

- `twoBlockOppositeTwistBlocks F m τ u` (from
  `TwoBlockJacquetConvergenceStatement`): block `0` twisted by `|det|^(-u)`
  and block `1` by `|det|^u`, on the same carriers. These are the source's
  `σ₁, σ₂`. This is not the Section (4.5) deformation of the first block, nor
  Shahidi's half-parameter family, nor an abstract equivalent
  representation.
- `TwoBlockJacquet.Sections F h τ_u` and `TwoBlockJacquet.inducedRep F h τ_u`
  (from `TwoBlockJacquetData`): the carrier and action of the canonical
  normalized lower parabolic induction
  `F.canonicalNormalizedOppositeParabolicInduced (succBlockShape m h)
  ((succBlockShape m h).blockTensor τ_u)`, acting by right translation. This
  is the source's `σ_u`, with covariance (4.6.1)
  (`TwoBlockJacquet.scalarSection_covariant`).
- `TwoBlockJacquet.jacquetFunction ψ ell μ f g` (from `TwoBlockJacquetData`):
  the Bochner integral over `x` in the rectangle `M((m 0 + 1) × (m 1 + 1))` of
  `tensorContraction ell (f(upperRadical h x * g)) * positiveKernel ψ x`.
  `upperRadical h x` is `(1 x; 0 1)`, and the kernel is the positive
  character `ψ(x_(m 0, 0))`, which equals the source's
  `θ[(1 x; 0 1)] = ψ(Σ u_(i,i+1))`
  (`TwoBlockJacquet.positiveKernel_eq_superdiagonal_upperRadical`). The
  source's integral with the positive kernel defines a `ψ̄`-functional, which
  is why `J` is required to be in the inverse-character space.
- The scalar evaluation uses the same linear maps `(ell i).val` on the
  twisted carriers. The published `twoBlockOppositeTwistFunctional` shows
  they remain inverse-character functionals of the twisted blocks, since
  determinant powers are trivial on unipotent matrices. As explained in the
  Markdown of `TwoBlockJacquetConvergenceStatement`, this replaces the
  source's evaluation of Whittaker functions at `e`.
- `rectangularMeasure ν.val (m 0 + 1) (m 1 + 1)` (from
  `Langlands.Representation.RankinSelberg.Measures`): the product of copies
  of the supplied self-dual Haar measure, one per matrix entry, the source's
  `dx`.

## Expected proof

A later proof task should assemble published results, with no further
premise:

- the ordinary convergence theorem
  `Langlands.RankinSelberg.twoBlockJacquetConvergence`, which gives the bound
  `C` and clause 1;
- `J(f) := jacquetFunction … f 1`, linear by `TwoBlockJacquet.jacquetFunction_add`
  (under the integrability of clause 1) and
  `TwoBlockJacquet.jacquetFunction_smul`;
- inverse-character equivariance from
  `TwoBlockDeformation.jacquetFunction_inducedRep_upperUnipotent`;
- the coefficient identity from `TwoBlockJacquet.jacquetFunction_inducedRep`;
- `J.val ≠ 0` from
  `TwoBlockDeformation.exists_section_jacquetFunction_one_ne_zero`, which
  applies because the twisted blocks are smooth.

The proposition does not assume induced Whittaker type, uniqueness of the
ambient functional, convergence, nonvanishing, an abstract inherited
functional or an integral comparison.

## Not claimed

The module proves nothing. The proposition does not state:

- the comparison part of the source's model assertion, that the coefficient
  image of `J` equals that of every other nonzero functional of `σ_u`, or
  that all elements of `W(σ_u; ψ̄)` are integral functions;
- a Whittaker model equivalence for `σ_u` or for reducible carriers;
- stable integrals, totality for arbitrary complex parameters, quotient
  unfolding, existence of factors, functional equations or
  multiplicativity.
