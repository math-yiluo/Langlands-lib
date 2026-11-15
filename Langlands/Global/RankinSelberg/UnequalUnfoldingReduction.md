# A conditional reduction of the unequal-rank unfolding statement

`Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingReductionStatement`
is the Prop-valued statement that four explicitly stated analytic
premises, assumed for every actual positive unequal-rank pair of
cuspidal realizations, imply the Library statement
`Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingStatement`
(Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2,
printed pp.205–207, PDF pp.208–210, source
`cogdell-2004-analytic-theory-gln`). The module also proves it:
`unequalUnfoldingReduction : UnequalUnfoldingReductionStatement`.
The premises remain open; this is a conditional result, not a proof of
`UnequalUnfoldingStatement`.

Provenance: derived. The conclusion is the existing Library statement;
the premises are the analytic inputs of Cogdell's argument, stated
for the Library's actual objects.

## The statement

`UnequalUnfoldingReductionStatement.{u}` is

`(∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
   (r t : ℕ) (h : t < r) (T : CuspidalOperatorRealization F r)
   (T' : CuspidalOperatorRealization F t), UnequalUnfoldingPremises F h T T')
 → UnequalUnfoldingStatement.{u}`.

`UnequalUnfoldingPremises F h T T'` is the conjunction of the four
premises below. Notation: `n = r + 1`, `m = t + 1`,
`φ = cuspFunction F T v`, `φ' = cuspFunction F T' v'`,
`W = cuspWhittaker F T ψ v`, `W' = cuspWhittaker F T' ψ⁻¹ v'`, tilde for
the Library's `dualFunction`, `w' = unfoldingWeyl F h`, `rect` for
`rectangularPoint`, and `N_m(F) \ GL_m(𝔸)` carries the Library's
`LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F m) _`
(ambient Haar and counting measure). "Standard" means
`IsStandardAdditiveCharacter`.

1. **E, `ProjectionWhittakerExpansion F h T`** (defined in
   `UnfoldingOrdinary`): for every standard `ψ`, `v` and
   `g ∈ GL_m(𝔸)`, the sum over `γ ∈ N_m(F) \ GL_m(F)` of
   `|det g|^{-(n-m-1)/2} W(diag(γ g, I_{n-m}))` converges
   unconditionally to `projection F _ ψ φ (diag(g, 1))`.
   Source: the displayed expansion of Cogdell p.205, "with convergence
   absolute and uniform on compact subsets".
2. **E', `DualProjectionWhittakerExpansion F h T`** (defined in
   `UnfoldingDual`): for every standard `ψ`, `v` and `g`, the function
   `x ↦ W̃(rect(g, x) w')` is integrable for `rectangleMeasure`, and the
   sum over `γ ∈ N_m(F) \ GL_m(F)` of
   `|det g|^{-(n-m-1)/2} ∫_x W̃(rect(γ g, x) w') dx` converges
   unconditionally to `dualProjection F _ ψ φ̃ (diag(g, 1))`. This is the
   author's formulation of the expansion behind Cogdell's p.207 remark
   that "one can unfold the definitions" and that "the extra unipotent
   integration is the remnant of P̃"; see `UnfoldingDual.md` for a
   hand check in the case `n = 3`, `m = 1`.
3. **G, `WhittakerGaugeIntegrable F h T T'`**: there is `C ≥ 0` such
   that for every standard `ψ`, all `v`, `v'` and `Re s > C`, the
   function `h ↦ W(diag(h, I)) φ'(h) |det h|^{s-(n-m)/2}` is integrable
   on `N_m(F) \ GL_m(𝔸)` (evaluated at quotient representatives).
   Source: Cogdell p.206, "This integral is absolutely convergent for
   Re(s) » 0 by the gauge estimates of [22, Section 13]".
4. **G', `DualWhittakerGaugeIntegrable F h T T'`**: there is `C ≥ 0`
   such that for every standard `ψ`, all `v`, `v'` and `Re s > C`, the
   function
   `h ↦ (∫_x |W̃(rect(h, x) w')| dx) |φ̃'(h)| |det h|^{Re s-(n-m)/2}`
   is integrable on `N_m(F) \ GL_m(𝔸)`. Source: Cogdell p.207, "As
   before, Ψ̃(s; W, W') is absolutely convergent for Re(s) » 0", in the
   global form of premise 3 with the dual cusp form `φ̃'` in place of
   its Whittaker function.

The bounds `C` in premises 3 and 4 are uniform over standard
characters and vectors, as the target statement requires.

## Proof

`unequalUnfoldingReduction` takes `C = max C₁ C₂` from premises 3 and
4. For `Re s > C` it applies `ordinary_unfolding` (module
`UnfoldingOrdinary`) with premises 1 and 3. For `Re s < -C` it applies
`dual_unfolding` (module `UnfoldingDual`) at `1 - s`, with premises 2
and 4, since `Re(1 - s) > 1 + C ≥ C₂`.

Both halves follow Cogdell's unfolding through the generic steps of
`UnfoldingSteps`:
unfolding the sum over `N_m(F) \ GL_m(F)` against the quotient
`GL_m(F) \ GL_m(𝔸)`, averaging over `N_m(F) \ N_m(𝔸)` (which turns the
cusp form `φ'`, respectively `φ̃'`, into its Whittaker function, with
the Library's mass normalizations cancelling exactly), and passing to
the Whittaker quotient `N_m(𝔸) \ GL_m(𝔸)` with `whittakerQuotientMeasure`.
The supporting modules are `UnfoldingMeasure`, `UnfoldingCoefficient`,
`UnfoldingWhittaker`, `UnfoldingGL`, `UnfoldingSteps`,
`UnfoldingOrdinary`, `UnfoldingDualGL` and `UnfoldingDual`.
