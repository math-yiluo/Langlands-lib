# Conductor preservation and the numerical surjectivity step

Worker 619, Task 7045. Namespace
`Langlands.Henniart.Extension.SupercuspidalConductor`, independent universes
`uK uW uV`.

## Imports and provenance

- `HenniartRankConductor` supplies the rank extension, its decomposition and
  rank specifications, the Weil-side conductor computation
  `weil_exponent_of_twist`, the epsilon unramified-twist lemma, and
  `firstFixedLevel_eq_of_isNewvectorConductor`. These results do not take the
  generic conductor premise. This module adapts only the two results that
  previously passed that premise to the newvector comparison.
- `HenniartNumericalStatement` supplies Henniart's numerical injection and
  surjectivity interfaces.
- `HenniartSupercuspidalConductorFiniteness` supplies the restricted
  newvector-conductor comparison.

The implementation adapts `HenniartRankConductor` and
`HenniartSurjectivityStepProof`. Its provenance is the existing route for
Henniart 2000, §4.3, using the surjectivity assertion of Henniart 1988,
Theorem 1.2. The arithmetic epsilon-exponent computation remains the
published Tate–Deligne calculation; this module adds no source assertion.

## Implemented proofs

`conductor_eq_of_pairEpsilon` chooses a representative of the supercuspidal
class and uses the new `exists_newvectorConductor_of_pairEpsilon`. The
published `firstFixedLevel_eq_of_isNewvectorConductor` identifies its
newvector level with `Numerical.conductor`.

`rankExtension_conductor` decomposes a Weil class into an unramified twist
of a unitary basis element using `rankExtensionBasis_spec` and
`rankExtensionBasis_rank`. For its candidate, it chooses an additive
character using `padicUnitaryAdditiveCharacterExists` and a self-dual measure
from the candidate's conditions. `candidate_character_generator` supplies
the trivial rank-one test, and `candidate_pairEpsilon` supplies matching
arithmetic and group epsilon exponents.
`LocalWeil.isArithmeticPairEpsilonFactor_of_generator` and
`weil_exponent_of_twist` identify the common exponent with the Artin
conductor plus `(k+1) n(ψ)`.
On the group side,
`isSupercuspidalPairEpsilonFactor_unramifiedTwist_left` uses the published
`RankinSelberg.unramifiedTwistEpsilon` to preserve that exponent under the
unramified twist. The new `conductor_eq_of_pairEpsilon` identifies the
group conductor. `sigma_rankExtension` identifies the resulting class
with the rank extension, and cancellation of the common additive-character
term proves equality with the Artin conductor.

`SurjectivityStepReductionStatement` is a derived Prop definition with the
same inputs as the published reduction except that its conductor premise is
`SupercuspidalPadicConductorExponentStatement.{uK,uV}`.
`surjectivityStepReduction` proves it. Normalized reciprocity supplies
`baseGeometricReciprocityProof`; the local-constant-system input supplies
the system. The rank extension is a numerical injection because of
`rankExtension_injective`, the new `rankExtension_conductor`, and
`rankExtension_twist` with
`unramifiedTwistIndependence_of_reciprocity`. The numerical-surjectivity
premise makes it surjective, and
`stableSurjectiveAt_of_surjective` gives the stable surjectivity step.

The conductor premise is used only through the new comparison for a
supercuspidal object over its canonical p-adic field. The module proves no
numerical-surjectivity or candidate-existence premise.
