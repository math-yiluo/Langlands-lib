# The cuspidal-isobaric pole order from completed pair poles

`Langlands.Global.cuspidalIsobaricPoleOrderLandauReduction` proves
`Langlands.Global.CuspidalIsobaricPoleOrderLandauReductionStatement`.
Its sole premise is `CuspidalPairPoleStatement.{u, uQ}`. The conclusion is
`CuspidalIsobaricPoleOrderStatement.{u, uQ}`, including existence of the
local data and completed functions and the pole order for every family
of completed representatives. Both universe parameters are retained.

## Proof

1. Apply `partialPairContinuationReduction` to the completed pair-pole
   premise and the published `cuspidalPairAbsoluteConvergence`. For
   each field `F`, this gives `PartialPairContinuationAt F`. The
   split-centre hypotheses supply unitary central characters by
   `cuspidalSplitCentreUnitaryCentralCharacter`. For a pair and a
   finite set `S` containing both exceptional sets, the continuation
   gives a meromorphic partial representative `L` whose values on
   `Re s > 1` are the exponential of the sum of the logarithmic Euler
   terms outside `S`. The sum restricted to the real interval `(1, 2)`
   is continuous by `differentiableOn_logSeries`.
   [Partial continuation](CuspidalPairPartialContinuation.md).
2. Apply `landauAsymptoticsReduction` to the same convergence and
   continuation data. At shift zero it gives limit `1` for the
   logarithmic sum divided by `log(1/(σ − 1))` when the first
   realization is contragredient to the second after identifying the
   ranks, and limit `0` otherwise, as `σ` approaches `1` from above.
   This step uses the squared power-trace positivity argument for
   the partial Euler products. [Exact boundary orders](CuspidalPairLandauOrders.md).
3. The private helper `order_eq_of_normalizedLog` recovers the order of
   `L` from this limit. The real ray tends to the punctured complex
   neighbourhood of `1`. An infinite order would make `L` vanish
   eventually on that ray, contradicting the exponential identity.
   For the resulting finite integer order `m`,
   `tendsto_div_log_of_meromorphicOrderAt` gives limit `−m` for the
   same normalized logarithm. Uniqueness of limits gives order `−1`
   in the contragredient case and `0` otherwise. Thus this `L` supplies
   the witness for `PartialPairNonvanishingAtOne F`.
   [Boundary logarithm asymptotics](../../Analysis/LogarithmicAsymptotics.md).
4. Apply `cuspidalIsobaricPoleOrder_of_partialPairNonvanishingAtOne`
   to the completed pair-pole premise and these fieldwise witnesses.
   The assembly reinstates the reciprocal-entire local factors for
   the upper order bound, uses the pair profile for the lower bound
   and pole criterion, and adds the constituent orders. The
   contragredient symmetry theorem identifies the pole criterion
   with the multiplicity counted by the target.
   [Isobaric assembly](CuspidalIsobaricPoleOrderReduction.md).

## Provenance

Getz and Hahn invoke their completed pair theorem for the isobaric pole
formula. The Lean implication follows that assembly and supplies the
partial-factor upper bound at `s = 1` through logarithmic asymptotics.
The partial witness here concerns split-centre-trivial cuspidal pairs
with irreducible admissible finite components at this one point. The
separate boundary nonvanishing statement in the Library concerns the
full line for unitary central characters.

- J. R. Getz and H. Hahn, *An Introduction to Automorphic Representations*
  (2024), (11.23), printed p. 308 (PDF p. 319), Theorem 11.7.1, printed
  p. 309 (PDF p. 320), and §11.8 through Lemma 11.8.1, printed pp. 311–312
  (PDF pp. 322–323), give the completed product, pair pole profile and
  isobaric formula. Registered source `getz-hahn-2024-automorphic-representations`.
- H. Jacquet and J. A. Shalika (1981), Theorem 4.1 and its proof in
  *On Euler Products and the Classification of Automorphic Representations II*,
  printed pp. 805–806 (PDF pp. 30–31), compare the logarithmic Euler
  series with the logarithm of the partial function in displays (2)–(7).
  The Lean helper uses uniqueness of that normalized limit to recover
  the order. Registered source `jacquet-shalika-1981-euler-ii`.
- P. Sarnak, *Nonvanishing of L-functions on Re(s) = 1* (2004), §1,
  display (5), IAS manuscript p. 3 (PDF p. 3), gives the four-factor
  product used in the imported positivity argument. The real
  singularity criterion used there is Hardy and Riesz, *The General
  Theory of Dirichlet's Series* (1915), Theorem 10, printed p. 10
  (PDF p. 26). Registered sources `sarnak-nonvanishing-line-one` and
  `hardy-riesz-1915-dirichlet-series`.
