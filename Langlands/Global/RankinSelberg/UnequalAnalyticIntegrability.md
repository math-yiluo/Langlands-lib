# Weighted integrability of cusp forms on `GL_n(F) \ GL_n(𝔸)`

Provenance: internal. This module supports the proof of
`Langlands.Global.RankinSelbergGlobal.UnequalAnalyticStatement` (Cogdell 2004, Theorem 2.1).
Convergence of the unequal-rank global integral for every `s` reduces to the finiteness of
`∫_{GL_n(F) \ GL_n(𝔸)} |f(g)| exp (-B |log |det g||) dg` for one cusp form `f` and all large
`B`. The second factor of the integrand (the projection) decays faster than every
`exp (-N |log |det g||)` (module `UnequalAnalyticProjection`). The quotient measure is the
Library's `AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F n)` on the actual
group-scheme points.

All declarations are in the namespace `Langlands.Global.RankinSelbergGlobal.UnequalAnalytic`.
`e n` is the Library homeomorphism `GeneralLinearGroupPoints.adelicHomeomorph F n` from the
actual adelic points `Points F n` to the adelic matrix group `AdelicGL F n`.

## Declarations

- `integrable_of_enorm_le`: if `f` is a.e. strongly measurable and
  `‖f x‖ₑ ≤ ofReal C · w x` with `∫⁻ w < ∞`, then `f` is integrable
  (`lintegral_mono`, `lintegral_const_mul'`).
- `lintegral_quotient_lt_top_of_cover` (**transfer of a weighted cover**): let `φ₀` on
  `GL_n(𝔸)` be continuous and left invariant under `GL_n(F)`. Let `t` be a measurable set
  meeting every rational orbit, such that `|φ₀| exp (-B |log |det||)` has finite integral over
  `t` for the image of the Haar measure of `Points F n` under `e n`. Then
  `q ↦ |φ₀ (e n (out q))| exp (-B |log |det (out q)||)` has finite integral over the
  quotient. Proof: the weight `w` on `Points F n` is left invariant under rational points (the
  invariance of `φ₀` and the product formula `detNorm_rational_mul`), so the integrand is its
  descent (`lift_eq_out`). The Library bound
  `LeftCosetSpace.lintegral_restrict_discreteQuotientMeasure_le` (with `A = univ` and the
  covering set `(e n)⁻¹ t`) bounds the quotient integral by `∫⁻_{(e n)⁻¹ t} w dHaar`. This is
  the given integral after `lintegral_map`, as in the Library proof
  `OperatorDeterminantSlice.lintegral_band_le_cover`.
- `exists_lintegral_quotient_lt_top`: for a cuspidal `OperatorRealization F n` `S` and
  `f : S.Space`, there is `B₀` with
  `∫⁻_{GL_n(F) \ GL_n(𝔸)} ‖f(e n (out q))‖ₑ exp (-B |log |det (out q)||) < ∞` for all
  `B ≥ B₀`. Combine `exists_weighted_cover` (module `UnequalAnalyticDecay`, with the Borel
  structure on `AdelicGL F n`) with the previous lemma. The measure `map (e n) Haar` is a Haar
  measure (`ContinuousMulEquiv.isHaarMeasure_map`), hence left invariant and finite on compact
  sets.
