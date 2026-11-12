# The rational geometric-lemma K0 expansion from the parabolic points statement

Module: `Langlands.Representation.Aubert.General.RationalGeometricK0Assembly`,
namespace `Langlands.Aubert.General.RationalPointFamily`. Author: Worker 4021.

`rationalGeometricK0Expansion_of_standardParabolicPoints` proves the published
target `RationalGeometricK0ExpansionStatement.{u, v}`, the whole unapplied
proposition at independent universes `u` and `v`. It takes one premise, the
published `StandardParabolicPointsStatement.{u}`. The declaration
`rationalGeometricK0ExpansionOfStandardParabolicPoints` packages the same
result as a def whose type is the implication.

## Proof

The proof introduces the target's binders exactly:

- the field and its local-field structure;
- `G`, `hG`, `T`, `i`, `hi`, with the target's instances `hG.isAffineHom` and
  `hi.isSplitSubtorus.mono` and the canonical `pointTopology`;
- local compactness, the nonarchimedean group structure and Hausdorffness;
- `ν`, `hν`, `StandardCocharacterStatement` and `HasRelativeRootSystem`;
- closedness of the standard unipotent, parabolic and Levi subgroups;
- continuity of the derived Levi projections;
- the unipotent limit-of-compact property;
- both finite-length preservation premises;
- the Weyl finiteness instance, `HasPointNormalizerComparison` and
  `HasPointCentralizerComparison`;
- the Coxeter matrix and actual Coxeter system;
- `RootLengthComparison` and `PositiveSimpleReflectionComparison` (neither is
  used);
- `actualLeviWeylIdentification`, `GeometricIntersectionDecompositions` and
  `GeometricTermFiniteLength`.

It then applies the published `geometricK0Expansion_of_points_of_balance`
(module `RationalGeometricK0Reduction`) to these premises and `hPoints`. The
epsilon input of that theorem is supplied for every `I`, `J` and actual
normalizer point `n` by `geometricEpsilon_mul_eq_one` (module
`RationalGeometricEpsilonBalance`). That theorem is applied to the decompositions
`isSemidirectDecomposition_of_standardCocharacterStatement` and the target's
own `HasRelativeRootSystem`, closedness and projection-continuity premises.

## Dependencies

Proof-body dependencies:

- `geometricK0Expansion_of_points_of_balance`, which uses the published
  support filtration, the orbit ordering by minimal-representative lifts, the
  orbit-grade comparison with `geometricTermFunctor`, and K0 filtration
  additivity;
- `geometricEpsilon_mul_eq_one`, the Haar balance through the common
  centralizer.

The only premise not in the target is `StandardParabolicPointsStatement`, the
Bruhat indexing of parabolic double cosets. These proof bodies invoke no
adjointness, cuspidal support, character independence or Langlands
classification. The imported module closure is larger.
