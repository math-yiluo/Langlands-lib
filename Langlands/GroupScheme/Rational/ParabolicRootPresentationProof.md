# Proof of existence and full independence of parabolic root presentations

Author: Worker 4487.

`parabolicRootPresentation` proves the published proposition
`ParabolicRootPresentationStatement.{u}` exactly, at arbitrary universe `u`.
The statement is the conjunction of three universal propositions. For every
field `k`, connected reductive `G` over `k`, and actual maps `p : P → G`,
`l : M → P` and `a : A → M` that are a rational parabolic, a rational Levi
and a split component, there is a compatible
`ParabolicRootPresentation p l a` of these specified maps. Any two compatible
presentations of the same maps have equal restricted root sets, strictly
positive root-combination cones and nonnegative root-combination cones in the
full real character space of `A`. For an isomorphism `e : A ≅ A'` compatible
with two component maps, the six character-pullback image equalities hold in
both directions. All presentation choices may vary. The target is a derived
structural comparison target motivated by Renard 2026 V.3.9 and V.3.14–V.3.15;
see the statement pair for its provenance.

The module also proves the existence conjunct alone as
`parabolicRootPresentationExistence : ParabolicRootPresentationExistenceStatement.{u}`,
so later users can import it by name.

## Implemented proof

The proof composes published theorems; it adds no hypothesis and no new
argument.

1. **Existence.** `parabolicRootPresentationExistence` applies the conditional
   construction `parabolicRootPresentationExistenceStatement_of_dynamic_centralizer`
   (module `Rational.ParabolicRootPresentationDynamicConstruction`) to four
   published unconditional theorems:
   - `genericMinimalParabolic : GenericMinimalParabolicStatement`
     (module `Rational.GenericMinimalParabolicProof`);
   - `relativeRootNegation : RelativeRootNegationStatement`
     (module `Rational.RelativeRootNegationProof`);
   - `parabolicDynamic : ParabolicDynamicStatement`
     (module `Absolute.ParabolicDynamicProof`);
   - `dynamicCentralizerReductive : DynamicCentralizerReductiveStatement`
     (module `Dynamic.CentralizerReductiveProof`).

   That construction builds one ambient cocharacter realizing both the image
   of the specified parabolic and the image of the specified Levi composite.
   It then gives a compatible presentation of the original maps `p`, `l` and
   `a`, not of a conjugate or replacement Levi.

2. **Actual reflections.** `relativeRootReflectionExistence_of_rootRankOneFactorization`
   (module `Rational.RootGeneratedCentralizerReduction`) turns the published
   unconditional `rootRankOneFactorization : RootRankOneFactorizationStatement`
   (module `Rational.RootRankOneFactorizationProof`) into
   `RelativeRootReflectionExistenceStatement`. Opposite factor pairs give
   integral relative-root reflection data for every maximal split torus.

3. **Aggregate.** `parabolicRootPresentationStatement_of_existence_of_reflections`
   (module `Rational.ParabolicRootPresentationIndependenceReduction`) takes
   the existence statement from step 1 and the reflection statement from
   step 2. From the reflections it derives presentation independence: equal
   restricted roots through intrinsic simple weights, and then both cone
   equalities by finite root-combination congruence. Compatible component
   pullback then gives the component-isomorphism conjunct. Together with
   existence this is the exact aggregate.

The theorem uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`. The proof keeps every feature of the target: arbitrary fields and
characteristic, nonsplit ambient groups, nonreduced relative roots, rank zero,
the actual specified maps, the full real character space and both cones.
