# The gauge integrability premises of the unequal-rank unfolding

`Langlands.Global.RankinSelbergGlobal.UnequalUnfoldingGaugeStatement.{u}`
is the Prop-valued conjunction of the premises G and G' of the published
`UnequalUnfoldingReductionStatement` (module
`Langlands.Global.RankinSelberg.UnequalUnfoldingReduction`), each quantified
over every actual positive unequal-rank cuspidal pair. No proof is supplied.

Provenance: derived. It restates, for all pairs, the two gauge premises
whose definitions are already in the Library.

## The statement

For every number field `F : Type u` with `CompactSpace (AdeleQuotient F)`,
naturals `t < r`, and actual cuspidal realizations
`T : CuspidalOperatorRealization F r` (rank `n = r + 1`) and
`T' : CuspidalOperatorRealization F t` (rank `m = t + 1`):

1. `WhittakerGaugeIntegrable F h T T'`: there is `C ≥ 0` such that for every
   standard additive character `ψ` (`IsStandardAdditiveCharacter`), all
   vectors `v`, `v'` and all `s` with `Re s > C`, the function
   `h ↦ W(diag(h, I_{n-m})) φ'(h) |det h|^{s-(n-m)/2}` is integrable on
   `N_m(F) \ GL_m(𝔸)`. Here `W = cuspWhittaker F T ψ v`,
   `φ' = cuspFunction F T' v'`, the function is evaluated at the quotient
   representatives `q.out`, and the quotient carries the Library's
   `LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F m) _`.
2. `DualWhittakerGaugeIntegrable F h T T'`: there is `C ≥ 0` such that for
   every standard `ψ`, all `v`, `v'` and all `s` with `Re s > C`, the real
   function
   `h ↦ (∫_x ‖W̃(rect(h, x) w')‖ dx) · ‖φ̃'(h)‖ · ‖|det h|^{s-(n-m)/2}‖`
   is integrable on `N_m(F) \ GL_m(𝔸)`. Here `W̃` is `dualFunction` of
   `W`, `w' = unfoldingWeyl F h`, `rect = rectangularPoint F h`, the inner
   integral is over `rectangleMeasure F (r - (t + 1)) (t + 1)`, and
   `φ̃' = dualFunction F (t + 1) φ'`.

Both bounds `C` are uniform over standard characters and vectors, as
`UnequalUnfoldingStatement` requires.

## Source

J. W. Cogdell, *Analytic theory of L-functions for GL_n* (2004), §2.2,
source `cogdell-2004-analytic-theory-gln`, printed p.206 (PDF p.209): the
unfolded ordinary integral "is absolutely convergent for Re(s) » 0 by the
gauge estimates of [22, Section 13] and this justifies the interchange",
where Cogdell's bibliography (printed p.227, PDF p.230) identifies [22] as
Jacquet, Piatetski-Shapiro and Shalika, *Automorphic forms on GL(3), I & II*,
Ann. Math. 109 (1979), 169–258. Printed p.207 (PDF p.210): "As before, Ψ̃(s; W, W')
is absolutely convergent for Re(s) » 0." Premise 1 is the integrability
over `N_m(F) \ GL_m(𝔸)` that justifies Cogdell's interchange before the
second unfolding; premise 2 is its dual analogue with the bounded dual cusp
form `φ̃'` in place of its Whittaker function and with the inner
rectangular integral of absolute values.

## Role

`UnequalUnfoldingReductionStatement` assumes E, E', G and G' for every
pair. A proof of this statement discharges G and G'. Together with proofs
of the expansions E (`ProjectionWhittakerExpansion`) and E'
(`DualProjectionWhittakerExpansion`) for every pair, the published theorem
`unequalUnfoldingReduction` then yields `UnequalUnfoldingStatement`.
