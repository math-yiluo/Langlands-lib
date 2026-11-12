# Henniart's construction from stable images, and the route to the correspondence

Author: Worker 4803. Module `Langlands.Correspondence.HenniartExtensionReduction`,
namespace `Langlands.Henniart.Extension`. Universes: `uK` (p-adic fields), `uW`
(Weil carriers and local constants), `uV` (supercuspidal carriers), and `uE` for
the local constants of an arbitrary construction statement. All are independent.

## Statements

### `HenniartConstructionReductionStatement.{uK, uW, uV}`

The implication

1. `CandidateExistenceStatement.{uK, uW, uV, uW, uK}` (Henniart 2000, Théorème 3.1
   with §§3.7–3.8, published by Worker 14 in `HenniartStableMapStatement`),
2. `StableCorrespondenceStatement.{uK, uW, uV, uW}` (Théorème 4.2 (a) and the
   bijectivity in (b)),
3. `UnramifiedTwistIndependenceStatement.{uK, uW, uV, uW}` (§4.4 with Henniart
   1993, §4.3),
4. `SupercuspidalUnitaryFiniteOrderTwistStatement.{uK, uV}` (module
   `HenniartExtensionInputs`),
5. `LocalClassField.CommonClosureReciprocityExistence.{uK}` (published normalized
   local reciprocity in a common closure),
6. `∀ p K eC, LocalFactor.NonabelianSystem.Exists.{uK, uW} K eC` (Deligne's local
   constants for every normalized family; the convention of the published
   `associatedTemperedFactor_of_gamma_and_existence`),
7. `RankinSelberg.UnramifiedTwistEpsilonStatement.{uK, uV, uV}` (published JPSS
   unramified-twist law for pair epsilon factors),
8. `ArithmeticPairUnramifiedTwistStatement.{uK, uW}` (module
   `HenniartExtensionInputs`)

implies `HenniartConstructionStatement.{uK, uW, uV, uW}`. That is: over every
p-adic field `K` some supercuspidal map is a supercuspidal correspondence
(`IsSupercuspidalCorrespondence`), and on every unitary class factoring through
a finite quotient it agrees with a stable image.

### `SupercuspidalCorrespondenceHenniartReductionStatement.{uK, uW, uV}`

`RankinSelberg.SupercuspidalLocalConverseStatement.{uK, uV, uV}` together with
inputs 1–8 implies the unchanged target
`Correspondence.SupercuspidalCorrespondenceStatement.{uK, uW, uV}`: for every
prime `p` and every `F : PadicField p`, there is exactly one supercuspidal
correspondence.

Neither statement asserts any of its hypotheses. Both are proved in this module
with the standard axioms only.

## Provenance

Internal. Henniart (2000), §4.4, printed p. 453 (PDF p. 15), defines `π(σ)` for
all irreducible `σ` by unramified twisting from the classes with determinant of
finite order. It derives Théorème 1.2 "par les arguments (faciles) de [He 4,
§4]", that is Henniart (1993), §§4.2–4.4, printed pp. 348–349. The first
statement formalizes that step from the components of Worker 14's
`HenniartStableMapStatement` and the standard inputs listed. The second combines
it with the published uniqueness from local converse (Henniart 1993, Théorème
4.1). The sources of the two new inputs are given in
`HenniartExtensionInputs.md`.

## Proof

`henniartConstructionReduction`. Fix `p` and `K`. Input 5 gives a normalized
family `eC`; input 6 gives a system `ε` for it. The published
`baseReciprocityCandidate K eC` is a geometric reciprocity candidate (published
`baseGeometricReciprocityProof`), compatible with `eC`
(`baseReciprocityCandidate_spec`). Call it `e`. The supercuspidal map is
`extensionMap K hSC` of module `HenniartExtension`. Its properties:

- rankwise bijective: `extensionMap_rankwiseBijective` (uses inputs 1–4 and `e`);
- dual compatible: `extensionMap_dual` (inputs 2, 3);
- with the geometric candidate `e`: rank one `extensionMap_rankOne`, determinant
  `extensionMap_determinant`, twists by all quasi-characters
  `extensionMap_twist`, and pair factors `extensionMap_pairFactors` for
  `(eC, ε)` (inputs 1, 2, 7, 8);
- agreement with the stable images: `extensionMap_agrees` (inputs 2, 3).

`supercuspidalCorrespondenceExistence_of_henniartConstruction` extracts
existence over each field from any construction statement, for any `uE`.
`supercuspidalCorrespondenceStatement_of_localConverse_of_henniartConstruction`
combines it with the published
`supercuspidalCorrespondenceStatement_of_localConverse_of_existence`.
`supercuspidalCorrespondenceHenniartReduction` composes the two reductions.

## Library correction carried by this contribution

`Langlands/Correspondence/BaseReciprocityCoherence.lean` declared an unnamed
local instance `TopologicalSpace F.Carrier`. In a common import closure it
received the same automatic name, `Langlands.Correspondence.instTopologicalSpaceCarrier_5`,
as the unnamed local instance of `ArithmeticSystemComparison.lean`. Any module
importing both, as the composite theorem here must, then failed to compile.
The instance is now named `baseReciprocityCoherenceTopology`. No statement,
definition or proof changes; no Library file referred to the automatic name.
