# The gauge integrability premises of the equal-rank unfolding

`Langlands.Global.RankinSelbergGlobal.EqualUnfoldingGaugeStatement.{u}` is the Prop-valued
conjunction of the premises G and G̃ of `EqualUnfoldingReductionStatement` (module
`Langlands.Global.RankinSelberg.EqualUnfoldingReduction`), each quantified over every
equal-rank pair of actual cuspidal realizations. No proof is supplied.

Provenance: derived. It restates, for all pairs, the two gauge premises defined in
`EqualUnfoldingReduction`, so that their proof can be routed as a separate task.

## The statement

The first conjunct says: for every number field `F : Type u` with
`CompactSpace (AdeleQuotient F)`, every `r : ℕ`, and all actual cuspidal realizations
`T T' : CuspidalOperatorRealization F r` (rank `n = r + 1`),
`EqualWhittakerGaugeIntegrable F T T'` holds. The second conjunct says the same, over the
same binders, for `DualEqualWhittakerGaugeIntegrable F T T'`.

Notation: `W = cuspWhittaker F T ψ v`, `φ' = cuspFunction F T' v'`, `e_n g = lastRow F r g`,
`|det g|^s = detPower F n g s`, and `Φ̂ = fourierTransform F n ψ Φ`. A tilde denotes the
Library's `dualFunction F n` (`f̃(g) = f(w ᵗg⁻¹)`). "Standard" means
`IsStandardAdditiveCharacter`. `N_n(F) \ GL_n(𝔸)` carries the Library's
`LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F n) _`, and functions on it are
evaluated at the quotient representatives `q.out`.

1. `EqualWhittakerGaugeIntegrable F T T'`: there is `C ≥ 0` such that, for every standard
   additive character `ψ`, all vectors `v`, `v'`, every `Φ ∈ schwartzBruhat F n` and every `s`
   with `Re s > C`, the function `g ↦ W(g) φ'(g) Φ(e_n g) |det g|^s` is integrable on
   `N_n(F) \ GL_n(𝔸)`.
2. `DualEqualWhittakerGaugeIntegrable F T T'`: there is `C ≥ 0` such that, for every standard
   `ψ`, all `v`, `v'`, every `Φ ∈ schwartzBruhat F n` and every `s` with `Re s > C`, the
   function `g ↦ W̃(g) φ̃'(g) Φ̂(e_n g) |det g|^s` is integrable on `N_n(F) \ GL_n(𝔸)`.

Both bounds `C` are uniform over standard characters, vectors and Schwartz–Bruhat functions,
as `EqualUnfoldingStatement` requires. The bound `C` may depend on `F`, `r`, `T` and `T'`.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.3, source
`cogdell-2004-analytic-theory-gln`. Printed p.210 (PDF p.213): after replacing the cusp form by
its Fourier expansion and unfolding to the integral of `W_φ(g) W'_φ'(g) Φ(e_n g) |det g|^s`
over `N_n(𝔸) \ GL_n(𝔸)`, "This expression converges for Re(s) » 0." Printed p.211 (PDF p.214):
"the right-hand side of the functional equation also unfolds as" the analogous integral at
`1 - s` of `W̃_φ W̃'_φ' Φ̂(e_n ·)`, "with convergence for Re(s) « 0."

Premise 1 is the integrability over `N_n(F) \ GL_n(𝔸)` that justifies the exchange of the
Fourier expansion and the integral in Cogdell's second unfolding. Premise 2 is the same input
for the contragredient data. It is stated at the variable `s` with `Re s > C`, so that applied
at `1 - s` it covers Cogdell's range `Re s ≪ 0`. In both premises the cusp form `φ'` (or
`φ̃'`) stands in place of its Whittaker function, since the integration is over
`N_n(F) \ GL_n(𝔸)`, before the averaging over `N_n(F) \ N_n(𝔸)`.

## Role

`EqualUnfoldingReductionStatement` assumes E, Ẽ, G and G̃ for every equal-rank pair. A proof
of this statement discharges G and G̃. Together with proofs of E
(`CuspidalWhittakerExpansionStatement`) and Ẽ (`DualCuspidalWhittakerExpansionStatement`), the
theorem `equalUnfoldingReduction` then yields `EqualUnfoldingStatement`. The lemmas
`integrable_equalWhittakerIntegrand_of_gauge` and
`integrable_dualEqualWhittakerIntegrand_of_gauge` in `EqualUnfoldingReduction` derive from G
(resp. G̃) alone the integrability of the Whittaker-side integrand of `EqualUnfoldingStatement`
(resp. of its dual).
