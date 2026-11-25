# Henniart's route with the conductor theorem only for supercuspidal p-adic representations

This module, in
namespace `Langlands.Henniart.Extension`, defines one proposition,
`SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement`, with universe
parameters `uK uW uV`. It proves nothing. It imports
`Langlands.Correspondence.HenniartStableMapStatement`,
`Langlands.Correspondence.HenniartNumericalStatement`,
`Langlands.Correspondence.SupercuspidalSpecification` and
`Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentStatement`.

## Statement

`Henniart.Extension.SupercuspidalCorrespondenceHenniartSupercuspidalConductorStatement.{uK, uW, uV}`
says that the following three propositions together imply
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`:

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}`;
2. `NumericalSurjectivityStatement.{uK, uW, uV}`;
3. `Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV}`.

Compare the published
`Henniart.Extension.SupercuspidalCorrespondenceHenniartThreeInputsStatement`
(module `Langlands.Correspondence.HenniartCorrespondenceThreeInputs`). Hypotheses 1
and 2 and the conclusion are the same as in that statement, in the same order and at
the same universe levels. Only hypothesis 3 is different. The published statement takes
`Conductor.ConductorExponentStatement.{uK, uV}`, JPSS 1981, Théorème (5.1), for every
generic representation over every nonarchimedean local field. Here hypothesis 3 is
`Conductor.SupercuspidalPadicConductorExponentStatement.{uK, uV}`: the same theorem
for supercuspidal representations of `GL_(n+1)(K)` only, where `K` is a p-adic field
in universe `uK` with its canonical topology, valuation and local-field structure. Its
Markdown file explains that it is a special case of `ConductorExponentStatement`. So
this statement has a weaker hypothesis than the published three-input statement, and
the published statement follows from it.

The statement does not assert any of its three hypotheses.

## Sources

The statement adds no new literature result. Hypothesis 3 is JPSS 1981
(Jacquet, Piatetski-Shapiro and Shalika, *Conducteur des représentations du groupe
linéaire*, Math. Ann. 256 (1981), 199-214, literature ID `jpss-1981-conductor`),
§(5.1), Théorème (i)-(iii), printed page 211, for supercuspidal representations over
p-adic fields. The Markdown file of
`Conductor.SupercuspidalPadicConductorExponentStatement` quotes that theorem and the
two results of JPSS 1983 (*Rankin-Selberg Convolutions*, Amer. J. Math. 105 (1983),
367-464, literature ID `jpss-1983-rankin-selberg`), Theorem (2.7)(ii) (printed
pages 390-391) and §(8.1), Proposition (i) (printed page 443), on which the planned
proof of that hypothesis rested. The hypothesis is proved as
`supercuspidalPadicConductorExponent` (module
`Langlands.Representation.Conductor.SupercuspidalPadicConductorExponentProof`). The Library statements document the sources of the
target and of hypotheses 1 and 2. The route as a whole follows Henniart 2000.

## Why the weaker hypothesis suffices

The proof of the published three-input statement uses `ConductorExponentStatement`
at one place only. The published proof passes it through this chain:

- `supercuspidalCorrespondenceHenniartThreeInputs`
  (module `HenniartCorrespondenceThreeInputs`), then
  `supercuspidalCorrespondenceHenniartFiveInputs`,
  `supercuspidalCorrespondenceHenniartRankOneInputs` and
  `supercuspidalCorrespondenceHenniartSixInputs` (modules
  `HenniartCorrespondenceFiveInputs`, `HenniartCorrespondenceRankOneInputs`,
  `HenniartCorrespondenceSixInputs`);
- from the six-input proof into `surjectivityStepReduction`
  (module `HenniartSurjectivityStepProof`), then `rankExtension_conductor` and
  `conductor_eq_of_pairEpsilon` (module `HenniartRankConductor`);
- and into `supercuspidalEpsilonConductorFinitenessPadicReduction` and
  `supercuspidalEpsilonConductorFiniteness_of_pairEpsilon` (module
  `HenniartPadicConductorFinitenessProof`).

Both branches end in `Henniart.Extension.exists_newvectorConductor_of_pairEpsilon`
(module `Langlands.Correspondence.HenniartConductorFinitenessProof`). That theorem
applies `Conductor.genericConductor_isNewvectorConductor_of_conductorExponentStatement`
(module `Langlands.Representation.Conductor.GenericEpsilonConductor`) to
`A.obj.representation`. Here `A : GeneralLinear.SupercuspidalRep` is a supercuspidal
representation of `GL_(k+1)(K.Carrier)` for a p-adic field `K` with its canonical
structures, and `A.property.2` is its supercuspidality. Hypothesis 3 covers exactly
this case.

A Lean check outside the Library showed that hypothesis 3 supplies the conclusion of
`genericConductor_isNewvectorConductor_of_conductorExponentStatement` for a
supercuspidal `π`, with the instances of `GenericEpsilonConductor`. It also showed
that `ConductorExponentStatement` implies hypothesis 3.

## Plan of the proof

The statement is proved as
`Henniart.Extension.supercuspidalCorrespondenceHenniartSupercuspidalConductor` (module
`HenniartSupercuspidalConductorReductionProof`, whose Markdown describes the proof as
carried out). The plan for that proof copies the chain listed above, with hypothesis 3
in place of `ConductorExponentStatement`:

1. a supercuspidal version of
   `genericConductor_isNewvectorConductor_of_conductorExponentStatement`, which adds
   the hypothesis `GeneralLinear.IsSupercuspidal π`;
2. versions of `exists_newvectorConductor_of_pairEpsilon`,
   `conductor_eq_of_pairEpsilon`, `rankExtension_conductor`,
   `surjectivityStepReduction` and
   `supercuspidalEpsilonConductorFiniteness_of_pairEpsilon` that take hypothesis 3;
3. the six-, rank-one-, five- and three-input reductions with hypothesis 3, which
   supply the other hypotheses from the same published proofs as before.

## Provenance

The statement is derived. It is the published
`SupercuspidalCorrespondenceHenniartThreeInputsStatement` (Henniart 2000's route as
formalized in the Library) with its third hypothesis restricted to the only case
that the route uses. It introduces no new mathematics.
