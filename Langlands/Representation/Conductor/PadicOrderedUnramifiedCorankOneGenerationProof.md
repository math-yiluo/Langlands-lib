# Jacquet's Lemma 3 over p-adic fields

Module `Langlands.Representation.Conductor.PadicOrderedUnramifiedCorankOneGenerationProof`.

`Langlands.Conductor.padicOrderedUnramifiedCorankOneGeneration` proves
`Langlands.Conductor.PadicOrderedUnramifiedCorankOneGenerationStatement.{uF, uV}`
([`PadicOrderedUnramifiedCorankOneGenerationStatement`](PadicOrderedUnramifiedCorankOneGenerationStatement.md))
exactly, with no additional premises. Its axioms are `propext`, `Classical.choice` and
`Quot.sound`.

## Proof

For a prime `p` and a p-adic field `K`, the statement is
`OrderedUnramifiedCorankOneGenerationAt K.Carrier` with the canonical structures
(`padicOrderedUnramifiedCorankOneGenerationStatement_iff`). It is
`orderedUnramifiedCorankOneGenerationAt_of_premises`
([`OrderedUnramifiedGenerationFromPremises`](OrderedUnramifiedGenerationFromPremises.md))
applied to the three premises proved over p-adic fields in
[`PadicTemperedTypePremises`](../RankinSelberg/PadicTemperedTypePremises.md):

- the classification with the identification of Whittaker models,
  `RankinSelberg.PadicTemperedType.genericStandardModule`;
- the pole bound (8.4), `RankinSelberg.PadicTemperedType.temperedPoleBound`;
- the tail divisibility (9.3), `RankinSelberg.PadicTemperedType.inducedTailLFactorAt`, in
  the two universe orders the induction uses.

The argument behind `orderedUnramifiedCorankOneGenerationAt_of_premises` is the double
induction of JPSS 1983, Proposition (9.4), for `π × I(x)`, followed by the generation of
the L-factor by corank-one integrals (JPSS 1983, Theorem (2.7)). It is described in the
Markdown of that module and of
[`TemperedTypeLFactorProof`](../../AllField/Representation/RankinSelberg/TemperedTypeLFactorProof.md).

Source: Jacquet 2012 (literature ID `jacquet-2012-conductor-correction`), Lemma 3, printed
page 519, quoted from JPSS 1983 (literature ID `jpss-1983-rankin-selberg`), Section 9.
