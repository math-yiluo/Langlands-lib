# Proof of the reduction of input (I4) to Henniart's candidate

The module proves `Langlands.Henniart.candidateCompatibleNumericalInjectionsReduction`, of type
`CandidateCompatibleNumericalInjectionsReductionStatement.{uK, uW, uV}` (module
`Langlands.Correspondence.HenniartCandidateBaseChangeCompatibility`): candidate existence
(`CandidateExistenceStatement.{uK, uW, uV, uW, uK}`) and the compatibility of the candidate with cyclic base
change of prime degree (`CandidateBaseChangeCompatibilityStatement`) imply the rank-bounded input (I4),
`CompatibleNumericalInjectionsStatement`. Besides the two premises, the proof uses only theorems proved in the
Library; it adds no hypothesis and no axiom.

## The proof

Write `hCE` for the first premise and `hBC` for the second. Fix `p`, a cyclic prime-degree step `S`, a bound
`N` and `hsurj : Numerical.SurjectiveBelowRank N`.

1. **Library inputs.** Normalized reciprocity (`LocalClassField.commonClosureReciprocityExistence`), and from
   it the base geometric reciprocity map of each p-adic field (`baseGeometricReciprocityProof`); local constants
   (`NonabelianSystem.exists_system`); the spectral conductor
   (`SpectralConductor.spectralConductorRankOneReduction` with
   `Ramification.Padic.finiteInertiaConductorRefinement` and
   `SpectralConductor.commonClosureRankOneConductor`); the exponent of pair epsilon factors
   (`RankinSelberg.pairEpsilonExponentReduction` with `RankinSelberg.equalRankEpsilonCharacterChange`); the
   conductor theorem for supercuspidal representations (`Conductor.supercuspidalPadicConductorExponent`); the
   finiteness of candidate sets derived from the last two
   (`Extension.SupercuspidalConductor.supercuspidalEpsilonConductorFiniteness_of_pairEpsilon`); and
   unramified-twist independence from `hCE` and normalized reciprocity
   (`Extension.unramifiedTwistIndependence_of_reciprocity`). These are assembled as in the proof of
   `Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor`.
2. **The candidate is a numerical injection where it is defined** (`hinj`): over every p-adic field `K` and
   for `hS : StableExistsAt K (k+1)`, `Extension.rankExtension K hS` is injective
   (`Extension.rankExtension_injective`, from `hCE`), preserves conductors
   (`Extension.SupercuspidalConductor.rankExtension_conductor`) and commutes with unramified twists
   (`Extension.rankExtension_twist`).
3. **Stable existence up to `N`** (`hstab`), over every p-adic field and in every rank `n ≤ N`, by strong
   induction on `n` (`PNat.strongInductionOn`). Rank one is `Extension.rankOneStage_of_reciprocity`. For
   `1 < n ≤ N` and every `r < n`: `r < N`, stable existence in rank `r` holds by induction, the candidate in rank
   `r` is surjective by `hsurj` and step 2, and `Extension.stableSurjectiveAt_of_surjective` gives
   `StableSurjectiveAt K r`. `Extension.choiceIndependenceStep_of_inputs` then gives rank `n`.
4. **The witnesses.** `φL k hk` and `φM k hk` are the candidates over `S.base` and `S.top` with the proofs of
   step 3, and `Ch` is the map that `hBC` supplies for `S`. They are numerical injections by step 2, and `Ch`
   is a weak cyclic base change by `hBC`.
5. **(CI1), giving `IsBaseChangeCompatible`.** For `k + 1 ≤ N`, `σ`, a restriction decomposition `m` and the
   bounds `τ.1 + 1 ≤ N` on its members, the (CI1) clause of `hBC` applies with the proofs of stable existence
   from step 3; the two `Multiset.pmap`s agree by `Multiset.pmap_congr`, since by proof irrelevance the
   candidate does not depend on the proof of stable existence.
6. **(CI2), giving `ReflectsGaloisInvariance`.** If `φM k hk τ` is fixed by every element of `S.Gal`, then for
   every `w`, the (CI2) clause of `hBC` rewrites `φM k hk (weilConjugate S w τ)` as a Galois conjugate of
   `φM k hk τ`, which equals `φM k hk τ`; injectivity (`Extension.rankExtension_injective`) gives
   `weilConjugate S w τ = τ`.
