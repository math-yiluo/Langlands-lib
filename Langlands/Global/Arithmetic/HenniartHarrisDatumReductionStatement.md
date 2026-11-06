# Reductions of the Harris datum targets to the weight-one CM characters

Worker 84. The module defines two implication propositions. Defining them
proves nothing.

- `Langlands.Global.HarrisDatumCharacterRealizationOfHalfWeightStatement.{uF,uE,uE',uL}`
  is `CMHalfWeightCharacterStatement.{uE'} → HarrisDatumCharacterRealizationStatement.{uF,uE,uE',uL}`.
- `Langlands.Global.HenniartHarrisDatumOfHalfWeightStatement.{uF}` is
  `CMHalfWeightCharacterStatement.{0} → HenniartHarrisDatumStatement.{uF}`.

The targets and the hypothesis are the published (or co-staged) propositions
of `HenniartHarrisDatumStatement` and `CMHalfWeightCharacterStatement`. Their
Markdown gives the sources.

## Provenance

These are internal decompositions of the H2 targets, in the style of the
published `CMRegularUnitPrescriptionOfInputsStatement`. The weight-one CM
characters are the only input of the character realization that the
published Library does not yet prove. They are needed only when `[E' : E]`
is even, for the half-integral normalization of Harris 1998, p.195 (see the
Markdown of `CMHalfWeightCharacterStatement`). Their existence rests on the
quadratic character of the CM extension over its totally real subfield
(Harris–Taylor 2001, proof of Corollary VII.2.8), a class-field input. The
implications keep that input explicit, so that the rest of the construction
can be proved and checked separately. The second implication uses the
universe-`0` instance because the common-base fields are in `Type`.

A proof of an implication proves neither its hypothesis nor its conclusion.
The conclusion follows only once `CMHalfWeightCharacterStatement` is proved.
