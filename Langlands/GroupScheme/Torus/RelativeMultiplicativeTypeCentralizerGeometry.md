# Geometry of centralizers of groups of multiplicative type

Worker 873.

This internal support module derives the geometry of the existing all-test
centralizer from the published diagonalizable fixed-ideal construction and
published fppf descent of closed subgroups. The base scheme and universe are
arbitrary. The source morphism need not be a closed immersion.

The affine coordinate algebra of a finitely presented affine group is finitely
presented. The published fixed-ideal quotient preserves finite presentation,
even when the ambient group is not smooth. For a smooth ambient group the
published infinitesimal lifting theorem makes that same quotient smooth.

Centralizer membership means commutation after every refinement of every test
scheme. Equality of the two product morphisms can be checked on a pulled-back
fppf cover, because representable scheme functors are fppf sheaves. Thus the
actual centralizer is exactly the subgroup descended from its base changes.
Published closed subgroup descent supplies its closed representative.
Uniqueness of all-test representatives transports geometric properties to any
other representative, and target locality descends those properties.

Over an affine base, the relative diagonalizable model obtained from the group
algebra over the integers is compared with the actual group algebra over the
base ring by the published base-change isomorphism. Its conjugation fixed
scheme represents the centralizer. An affine open cover handles a diagonalizable
source over an arbitrary base, and the fppf splitting cover in the relative
multiplicative-type predicate handles a general source.

This is an internal derivation, not a transcription of Conrad's torsion-density
proof. It does not establish reductivity of the relative identity component.

`relativeMultiplicativeTypeCentralizer_isClosedRepresentable_of_affine` proves closed
representability for any relatively affine ambient group, with no finiteness
or smoothness hypothesis. The final two theorems,
`relativeMultiplicativeTypeCentralizer_locallyOfFinitePresentation` and
`relativeMultiplicativeTypeCentralizer_smooth_of_smooth`, prove the stated properties for
every all-test representative, assuming the corresponding property of the
ambient group. Each descends first from affine open charts of a diagonalizable
model, then from the fppf splitting cover. The local instances use the published
fppf target-locality theorem and Mathlib's flat descent of finite presentation
and smoothness. No closedness hypothesis on the source homomorphism is needed
for these conclusions.

`relativeMultiplicativeTypeCentralizerClosedModel` chooses the actual closed
representative. Its fields are the group scheme, inclusion, all-test
representing property and closedness. The finite-presentation and smoothness
theorems apply to this chosen model as well as to every other representative.
This construction uses classical choice from the closed-representability
theorem; it asserts no canonical choice or functoriality of the choice.

The imported constructions used here are
[`RelativeCentralizerSmooth`](RelativeCentralizerSmooth.md),
[`RelativeCentralizerDescent`](RelativeCentralizerDescent.md),
[`RelativeMultiplicativeType`](RelativeMultiplicativeType.md),
[`DiagonalizableBaseChange`](DiagonalizableBaseChange.md), and
[`FppfLocalAtTarget`](../../AlgebraicGeometry/Morphisms/FppfLocalAtTarget.md).
These are the provenance of this internal support unit. The exact relative
centralizer statement and its imports are unchanged.

The existing smooth-model API remains in `RelativeMultiplicativeTypeCentralizerModel`. The `ClosedModel` construction here retains its distinct `ClosedRepresentative` result without an ambient smoothness assumption. Shared fppf descent lemmas are imported from that existing module.
