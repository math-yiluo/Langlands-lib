# Published inputs for the two-block L-polynomial descent

Author: Worker 465.

This module assembles existing closed Library theorems for the conditional
two-block L-polynomial rank descent. It proves seven of that descent's twelve
inputs and transports its conclusion to independent original carrier universes.
The three analytic bases, restricted reverse divisibility, and high-ramification
vanishing remain explicit hypotheses of the resulting implication. The module
does not prove the closed `TwoBlockLFactorMultiplicativityStatement`.

All declarations below lie in
`Langlands.RankinSelberg.TwoBlockLVerifiedInputAssembly`.

`equalRankReverseAt.{uF,uV,uW}` proves the existing fieldwise predicate
`TwoBlockLConditionalAssembly.EqualRankReverseAt F ψ ν` for every canonical
p-adic field, nontrivial unitary additive character and supplied self-dual Haar
measure. Its proof applies the published
`equalRankRankOneExtensionLDivisibility.{uF,uV,uW}`. The two predicates have
definitionally equal telescopes: the conditional descent's private scalar lift
is the same action obtained by conjugating `rankOneCharacter χ` through
`ULift.moduleEquiv.symm`. The ordered upper family, its block shape, both
polynomial certificates, and `Pbase ∣ Pind` are retained. No strict-rank lemma,
pair-order identification, or additional analytic premise is used here.

`AvailableInputs.{uF,u}` is an internal proposition bundling the following
seven exact inputs at the stable carrier universe `max uF u`.
`availableInputs.{uF,u}` proves the conjunction using the indicated imported
closed theorems.

| Input in the conditional descent | Imported proof |
| --- | --- |
| Fieldwise equal-rank reverse comparison | The endpoint adapter `equalRankReverseAt` above |
| Common symmetric L-polynomial existence | `Langlands.RankinSelberg.symmetricLPolynomialExists` |
| Equal-rank swap for two stable carriers | `Langlands.RankinSelberg.equalRankFactorSwap` |
| Full normalized product Whittaker type | `Langlands.RankinSelberg.normalizedProductWhittakerType` |
| Scalar rank-one Whittaker type | `Langlands.RankinSelberg.rankOneWhittakerType` |
| Equal-rank swap for a scalar and a stable carrier | `Langlands.RankinSelberg.equalRankFactorSwap` at scalar universe zero |
| Actual continuous characters of unbounded conductor | `Langlands.HarmonicAnalysis.padicQuasicharacterUnboundedConductor` |

The common-existence theorem supplies one polynomial with existence witnesses
and universality over compatible quotient measures. Full normalized type
includes admissibility, group-algebra finite generation, and a linear
equivalence of the entire functional space with the scalars. Character
existence concerns actual continuous quasicharacters and their canonical
conductors. These assertions are conclusions of imported theorems, with no
new hypothesis in `availableInputs`.

`twoBlockLFactorMultiplicativity_of_remainingInputs.{uF,uV,uW}` concludes exactly
`TwoBlockLFactorMultiplicativityStatement.{uF,uV,uW}` under these five hypotheses:

- `TwoBlockLDominantRankStatement`;
- `TwoBlockLAdjacentRankStatement`;
- `TwoBlockLRankOneStatement`;
- `RankOneExtensionLDivisibilityStatement`;
- `WhittakerTypeHighlyRamifiedLVanishingStatement`.

The first four are instantiated with field universe `uF` and both carrier
universes `max uF uV uW`. The high-ramification input has field universe `uF`,
scalar first carrier universe zero, and second carrier universe
`max uF uV uW`. These are explicit mathematical assumptions of this theorem;
their proposition definitions and pending proof tasks supply no witnesses.

The proof takes `availableInputs` at `u := max uV uW`, passes its seven
components and the five hypotheses to
`TwoBlockLConditionalAssembly.twoBlockLMultiplicativity_of_inputs_commonUniverse`,
and applies the published
`Langlands.RankinSelberg.twoBlockLFactorMultiplicativity_of_commonUniverse`.
The latter lifts the original test and entire dependent ordered block family
through actual representation equivalences, then transports the certified
polynomials back to the original carriers. It preserves the polynomial
equation `X^e * ∏ i, Pi i = Q * P`. Thus the final implication has independent
`uF`, `uV`, and `uW`, arbitrary positive ranks in both orders, arbitrary reducible
Whittaker-type inputs, the original character and supplied Haar measure, and
the actual upper canonical normalized induction.

Provenance is internal composition of the named published declarations. This
module introduces no new integral comparison or literature claim. The
rank-descent proof and its JPSS Section 7 provenance remain in
[TwoBlockLConditionalAssembly](TwoBlockLConditionalAssembly.md), while the
endpoint's independent analytic proof remains in
[EqualRankRankOneExtensionDivisibilityProof](EqualRankRankOneExtensionDivisibilityProof.md).
It imports no unrestricted two-block or finite-block L-multiplicativity proof
and no later Section 9.3 tail theorem. The conditional conclusion does not
discharge the five remaining hypotheses or complete the parent proof task.
