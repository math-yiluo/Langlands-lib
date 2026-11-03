# Actual ambient half-modulus in Levi-in-Levi induction

This internal normalization adapter compares the already defined
`leviNormalizedInductionFunctor` with inflation followed by the actual ambient
positive half-modulus twist and raw smooth induction. It is derived from
`Parabolic` and the published `SubgroupOfModulus` transport laws; it claims no
geometric orbit or graded-piece comparison.

Let `G` be a locally compact nonarchimedean group, let `M` and `N` be closed
subgroups, and suppose `N`, `Q`, and `L` are contained in `M`. Supply the actual
semidirect decomposition of `Q.subgroupOf M` into `L.subgroupOf M` and
`N.subgroupOf M`, and an ambient normalizer inclusion
`hQN : Q ≤ normalizer N`. This inclusion concerns the actual subgroups,
not an assumed character comparison. It is already forced by `N ≤ M`,
`Q ≤ M` and the supplied decomposition: map each element of
`normalizer (N.subgroupOf M)` through the published
`subgroupOfNormalizerMap`. The adapter takes the ambient inclusion explicitly;
it does not add a representation-theoretic premise to the host expansion.

`ambientInductionCharacterInside` composes the actual
`HaarModulus.closedHalfCharacter N hN Q hQN` with
`subgroupOfContinuousEquiv hQM`. Its kernel is open because it is the preimage
of the ambient half-character's open kernel under this continuous equivalence.
It uses the canonical positive square root, with no arbitrary character input.

`inductionCharacter_subgroupOf_eq_ambient` identifies this smooth character
with the character used for induction inside `M`. Extensionality reduces its
homomorphism equality to the published `closedHalfCharacter_subgroupOf`;
proof irrelevance identifies the open-kernel certificates and normalizer
proofs.

`ambientLeviInductionFunctor` first pulls a smooth `L`-representation back to
`L.subgroupOf M`, inflates through the supplied decomposition's actual Levi
projection, twists on the entire `Q.subgroupOf M`, and takes raw smooth
induction to `M`. `leviNormalizedInductionFunctor_eq_ambient` unfolds the
existing induction definitions and substitutes the proved character equality.
`leviInductionNormalizationIso` is the natural isomorphism furnished by that
functor equality. The group universe and representation-carrier universe are
independent, and the resulting carrier universe is `max uG uV`.

`leviNormalizedInductionEval` evaluates an actual covariant function on `M`.
For every `q : Q.subgroupOf M` and `x : M`,
`leviNormalizedInduction_covariant_ambient` gives the covariance law

`f(q x) = δ_N(eQ(q))^(1/2) • A(eL(projection(q)))(f(x))`,

where `eQ` and `eL` are the actual subgroupOf continuous identifications and
`δ_N` is the ambient actual Haar modulus of conjugation on `N`.
Its proof specializes `normalizedInductionFunctor_covariant` and substitutes
`closedHalfCharacter_subgroupOf`. The right-translation and morphism-evaluation
lemmas unfold the existing constructions: the target group acts by
`(g f)(x) = f(x g)`, and a map `φ` acts by `(i(φ) f)(x) = φ(f(x))`.
These are formulas on the original induced-function carrier.

The twist remains after inflation. No modulus factorization through the Levi
projection, unimodularity statement, smoothness of that projection, or
compact/full-induction comparison is asserted. In the geometric target, the
subgroups are the actual target parabolic, Levi and radical intersections;
their containment in the ambient Levi follows from their intersection
definitions. This adapter concerns the same radical in two ambient groups.
Both orbit Haar corrections, distinct-radical modulus balance, actual
geometric filtration and normalized graded-piece identification remain open.
It does not prove `RationalGeometricK0ExpansionStatement`.

The proof bodies use subgroup transport, the actual half-modulus transport law,
and equality of functors. Transitively, `closedHalfCharacter_subgroupOf` uses
the same-radical restricted Haar-character comparison, whose proof applies
`Geometric.haarChar_eq_of_conjugacy` to `subgroupOfContinuousEquiv`.
That theorem is invariance of the actual Haar scaling scalar under a continuous
group isomorphism. The scalar's positive square root is the published one in
`Jacquet.PositiveCharacter`. No geometric lemma, adjointness, cuspidal support,
character independence or Langlands classification occurs in this proof route.
The imported `SubgroupOfModulus` includes `Parabolic` and its broader
representation-theory import closure, including `Jacquet.Localization`,
`Induction.Definitions`, `Category.Twist`, `CompactCoefficient.GroupTransport`,
`Aubert.SubgroupTransition` and `Jacquet.LocalizationExactnessStatement`.
The present proofs unfold the actual functor constructions and use their
intrinsic formulas; they do not invoke those other statement targets.

Author: Worker 184.
