# Proof of relative finite-morphism descent

Worker 105 authored this proof, reused here by Worker 1568 with the
published diagram-helper names.

`relativeFiniteDescent` proves exactly
`Langlands.AlgebraicGeometry.AffineLimit.RelativeFiniteDescent`
in `SchemeLimitRelativeFiniteStatement`. The statement's paired
Markdown records the original source, the derived strengthening and the
retained hypotheses.

The proof reuses `SchemeLimitModel.Geometry.morphismDiagram` and
`morphismDiagram_cartesian` from `SchemeLimitFiberLoci` for the actual natural
transformation of the two base-change diagrams and its Cartesian transition
squares. The helper `locallyOfFiniteType_baseChangeMap` from
`SchemeLimitRelativeClosedImmersionProof` supplies local finite type of the
components by base change.

For affine target `Y`, the limit of the affine base diagram is affine,
so the limiting finite morphism has affine source. The proved
`exists_isAffine_level` supplies a stage `i` at which the source is affine.
Restrict both actual diagrams to `Over i`, using its forgetful functor.
Every restricted source is affine because its projection to the affine
source at `i` is an affine morphism; every restricted target is affine.
Mathlib's cofilteredness of `Over i` and initiality of `Over.forget i`
construct the required index-category and limit witnesses. The original
limit morphism and cone equations are retained. At the identity object
`Over.mk (𝟙 i)`, the component is locally of finite type. The proved
`affineDiagramFiniteDescent` supplies a restricted stage and an
actual arrow to it; its underlying original stage has a finite morphism.

For arbitrary `Y`, quasi-compactness over the affine base supplies a
compact underlying space and hence a finite affine subcover. The actual
chart pullback squares transfer the limiting finite morphism to each
chart. The affine-target lemma gives a stage for each chart. A common
lower bound of these finitely many stages, with actual arrows, preserves
each chart's finite morphism by the Cartesian transition squares.
The proof constructs the base-changed open cover using `baseChangeCover`,
transports each chart morphism to the canonical pullback morphism through
the actual pullback isomorphism, and applies target locality of finite
morphisms. This gives a finite morphism at that one common stage.

Conversely, `cone_baseChangeMap_isPullback` identifies the actual limiting
morphism as a base change of any stage morphism. Stability under base
change gives the reverse implication. The proof uses no affineness or
separatedness assumption on the original models and no injectivity of
ring transitions. The statement's original-ring specialization and the
other clauses of Theorem 3.4(2) remain separate obligations.
