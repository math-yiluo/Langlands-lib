# Closed-immersion pullback of ample line bundles

This module proves the published proposition
`Langlands.AlgebraicGeometry.Picard.ClosedImmersionPullbackAmpleStatement`
as `Langlands.AlgebraicGeometry.Picard.closedImmersionPullbackAmple`:
for every closed immersion `i : Z ⟶ X` and ample line bundle `L` on `X`,
the actual line-bundle pullback `((LineBundle.pullback i).obj L)` is ample.
Schemes and universe are arbitrary. This includes empty schemes, nonreduced
closed subschemes, and closed immersions not of finite presentation.
The target and its imported definitions are unchanged.

The geometric argument follows Stacks Project Lemma 28.27.3, tag
[01PU](https://stacks.math.columbia.edu/tag/01PU), in the registered source
`stacks-ample-powers-restriction-quasiaffine-2026-10-24`, file `01PU.html`.
The tensor comparison and section transport below are internal constructions
for the Library's actual sheaf tensor and its whole generation opens.

`actualPullbackTensorPowIso` constructs an isomorphism
`pullback f (tensorPow M n) ≅ tensorPow (pullback f M) n`
for every scheme morphism `f`, module sheaf `M`, and natural exponent `n`.
At degree zero it uses the published `pullbackUnitIso`. At each successor
it uses the canonical `pullbackTensorComparison`, whose invertibility is
proved by the imported
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, then applies the
tensor functor to the identity and the preceding power isomorphism.
This respects the actual right-associated powers and their trailing
structure-module unit.

`LineBundle.pullbackPowSection` applies the published actual
`pullbackSection` to a section of `tensorPow L.obj n`, then applies the
global component of `actualPullbackTensorPowIso`. Its result is a section
of the corresponding power of the actual pulled-back line bundle.
The construction applies to all scheme morphisms and all natural exponents,
including zero.

`LineBundle.sectionOpen_pullbackPowSection` proves that the entire generation
open of this section is the inverse image of the original generation open.
First, the published
`Langlands.SchemeModule.trivializationOpen_mapIso` from
`Langlands.AlgebraicGeometry.Picard.AmpleIsoProof` removes the transport
isomorphism without changing the whole open. Then the published
`Langlands.SchemeModule.lineBundlePullbackSectionOpen` from
`Langlands.AlgebraicGeometry.Modules.PullbackSectionOpenProof` identifies the
generation open of the actual pulled-back section. Its rank-one hypothesis
is discharged by the published
`Langlands.AlgebraicGeometry.Picard.tensorPow_isLocallyFreeRankOne` from
`Langlands.AlgebraicGeometry.Picard.TensorRankOneProof`.
This equality holds for every morphism and exponent, without an ampleness
or closed-immersion hypothesis.

For `closedImmersionPullbackAmple`, a closed embedding into the compact
space underlying `X` gives compactness of `Z` via
`i.isClosedEmbedding.compactSpace`. At a point `z` of `Z`, ampleness on `X`
supplies a positive exponent `n` and power section `s` whose entire
generation open contains `i z` and is affine. Use `L.pullbackPowSection i s`
with the same exponent and positivity witness. The whole-open equality
just proved gives membership of `z`. It also gives affineness, because
`ha.preimage i` says that the inverse image of the affine open is affine
along a closed immersion, using its affine-morphism instance. Thus the
proof establishes exactly both clauses of the published ampleness
predicate for the pulled-back bundle.
