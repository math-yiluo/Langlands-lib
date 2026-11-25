# Henniart candidate finiteness with the supercuspidal conductor premise

Namespace
`Langlands.Henniart.Extension.SupercuspidalConductor`, independent universes
`uK uV`. This module proves two conditional lemmas and changes no existing
declaration.

## Imports and provenance

- `Representation.Conductor.SupercuspidalPadicGenericConductor` supplies the
  new comparison between the generic conductor and the newvector level under
  the supercuspidal p-adic conductor premise.
- `Correspondence.HenniartConductorFinitenessProof` supplies
  `Extension.trivialRankOneEquiv`, the epsilon-factor and central-character
  interfaces, and their underlying constructions. Its original conductor
  comparison is adapted here with the restricted premise.
- `Correspondence.PadicSupercuspidalFinitenessProof` supplies
  `CompactOpenFiniteness.centralLevelStratum_finite`.

This is an internal adaptation of `HenniartConductorFinitenessProof` and
`HenniartPadicConductorFinitenessProof`, following Henniart 2000, §4.3. The
published modules document the original sources: the dependence of the
epsilon exponent on the additive character is the Bushnell–Henniart–Kutzko
input; the least-level interpretation is restricted JPSS 1981 (5.1);
bounded-level finiteness is the p-adic Bernstein–Zelevinsky consequence.
No additional source theorem is asserted here.

## Implemented proofs

`exists_newvectorConductor_of_pairEpsilon` takes
`PairEpsilonExponentStatement.{uK,uV,0}` and
`SupercuspidalPadicConductorExponentStatement.{uK,uV}`. For a supercuspidal
object `A`, a self-dual measure and a certified epsilon monomial against the
trivial rank-one object, it gives a natural newvector conductor equal to
`m - (k+1) n(ψ)`.

It first uses `trivialRankOneEquiv`, epsilon invariance under representation
equivalence, and `isPadicSymmetricEpsilonFactor_of_le` to express the second
member as `rankOneCharacter 1`. Genericity for the original and scaled
characters follows from
`SupercuspidalLFactorCharacterization.isGeneric_of_isSupercuspidal`.
`UnramifiedUnitary.exists_scale_hasIntegerConductor` supplies a scaling to
conductor `𝔒`. `genericConductor_eq` reads the original epsilon exponent,
and `genericPairConductor_eq_of_pairEpsilonExponentStatement` identifies
the original and scaled conductors, using the generic trivial character
from `UniformRankOneTwist.isGeneric_rankOneCharacter_one`.
The new bridge
`genericConductor_isNewvectorConductor_of_supercuspidalPadic` then applies
to `A.obj.representation` with the actual supercuspidality proof
`A.property.2`. This is the only use of the conductor premise.

`supercuspidalEpsilonConductorFiniteness_of_pairEpsilon` proves the published
`SupercuspidalEpsilonConductorFinitenessStatement` from those same two inputs.
It identifies the scalar group with the center, using
`scalarEmbedding` and `Matrix.GeneralLinearGroup.center_eq_range_scalar`,
and transports the prescribed scalar character to a character of the center.
The prescribed exponent gives the bound
`b = (m - (k+1) n(ψ)).toNat`. The first lemma places every member of the
candidate stratum at that newvector level. `supercuspidalCentralActsBy_iff`
supplies the central action, and `firstFixedLevel_le_iff` supplies the
bounded-level condition. Thus the stratum is a subset of the finite set
given by `centralLevelStratum_finite`.

Both arguments retain the canonical p-adic topology, valuation and local-field
structures. Neither assumes a conductor assertion for a nonsupercuspidal
representation or for a field outside this p-adic scope.
