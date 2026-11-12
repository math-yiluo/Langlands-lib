# The surjectivity step from Henniart's numerical theorem

Author: Worker 4803. Module `Langlands.Correspondence.HenniartSurjectivityStepProof`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW` (Weil
carriers, also the local-constant systems), `uV` (supercuspidal carriers), independent.

## Statement: `SurjectivityStepReductionStatement.{uK, uW, uV}`

The implication below, proved as `surjectivityStepReduction`:

```
CandidateExistenceStatement.{uK, uW, uV, uW, uK} →
LocalClassField.CommonClosureReciprocityExistence.{uK} →
(∀ p K eC, NonabelianSystem.Exists.{uK, uW} K eC) →
NumericalSurjectivityStatement.{uK, uW, uV} →
(∀ p K, LocalFactor.ConductorExponent.SpectralConductorStatement.{uK, uW} K) →
RankinSelberg.PairEpsilonExponentStatement.{uK, uV, 0} →
Conductor.ConductorExponentStatement.{uK, uV} →
SurjectivityStepStatement.{uK, uW, uV, uW}
```

The conclusion is the published component of `HenniartStableMapStatement` (Henniart
2000, §4.3, last sentence): for every p-adic field `K` and rank `n`, if every unitary
irreducible Weil class of dimension `n` factoring through a finite Galois quotient has
a stable image (`StableExistsAt K n`), then every unitary supercuspidal class of
`GL_n(K)` with central character of finite order is the stable image of such a class
of dimension `n` (`StableSurjectiveAt K n`). It is one of the inputs of the published
entry `SupercuspidalCorrespondenceHenniartInductionStatement`. The entry of this
contribution, `SupercuspidalCorrespondenceHenniartFinalStatement` (module
`HenniartCorrespondenceFinal`), uses `surjectivityStepReduction` to discharge that input.

The hypotheses are published Library statements, and the statement asserts none of them:

- `CandidateExistenceStatement` (Henniart 2000, Théorème 3.1 with §§3.7–3.8), the
  candidates at finite quotients;
- `CommonClosureReciprocityExistence` and `NonabelianSystem.Exists` (local class field
  theory; Deligne's local constants for every normalized family);
- `NumericalSurjectivityStatement` (Henniart 1988, Théorème 1.2, second assertion:
  every injection of the irreducible Weil classes of dimension `n` into the
  supercuspidal classes of `GL_n` that preserves conductors and commutes with
  unramified twists is surjective);
- `SpectralConductorStatement` (Tate 1979, (3.4.5); Deligne 1973, (5.5.2)): the
  exponent of the epsilon factor of a local constant is `a(V) + n(ψ) dim V`;
- `PairEpsilonExponentStatement` (Bushnell–Henniart–Kutzko 1998) and
  `ConductorExponentStatement` (JPSS 1981, Théorème (5.1)).

## Proof

Fix `K`, `n = k + 1` and `hS : StableExistsAt K n`. Local reciprocity gives a normalized
family `eC`, its bottom geometric reciprocity candidate `e`
(`baseGeometricReciprocityProof`) and a local-constant system `ε`. The published
`unramifiedTwistIndependence_of_reciprocity` gives unramified-twist independence. The
map `rankExtension K hS` (module `HenniartRankExtension`) is a numerical injection
(`Numerical.IsNumericalInjection`):

- injective: `rankExtension_injective`;
- conductor-preserving: `rankExtension_conductor` (module `HenniartRankConductor`);
- compatible with unramified twists: `rankExtension_twist`.

Henniart's numerical surjectivity makes it surjective, and
`stableSurjectiveAt_of_surjective` (module `HenniartSurjectivityTransfer`) gives
`StableSurjectiveAt K n`.

## Provenance

Internal. Henniart (2000), §4.3, last sentence (printed p. 453, PDF p. 15): the
surjectivity in rank `n` follows from Henniart (1988), Théorème 1.2 (printed p. 498,
PDF p. 3). That theorem says that an injective map from the irreducible Weil classes of
dimension `n` to the supercuspidal classes of `GL_n` exists which preserves conductors
and is compatible with twisting by unramified characters, and that "Toute telle
application est bijective". Henniart (2000) gives no further detail. The Lean proof builds the required injection from the stable images by
unramified twists (§4.4) and proves its three properties from the inputs above.

## Supporting modules

`HenniartRankExtension`, `HenniartFiniteTwist`, `HenniartSurjectivityTransfer`,
`HenniartRankConductor`; each has its own Markdown. `HenniartRankConductor` also uses
`exists_newvectorConductor_of_pairEpsilon` from `HenniartConductorFinitenessProof`.
That module is a supporting module of the same contribution and is not yet in the
Library.
