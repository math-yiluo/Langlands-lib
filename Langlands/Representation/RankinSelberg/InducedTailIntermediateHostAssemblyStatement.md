# Exact prerequisites for the intermediate-tail span assembly

`InducedTailIntermediateHostAssemblyStatement` is an internal implication
collecting the five separately owned inputs used to assemble the unchanged
`InducedTailIntermediateRankSpanStatement`. This proposition does not prove
any of its inputs or the closed intermediate-tail span theorem.

The premises, in order, are:

1. `InducedTailIntermediateDiagonalExtensionSpanStatement` at field universe
   `uF`, induced-carrier universe `max uF uV₁ uV₂`, and test-carrier universe
   `uW`. It retains the actual diagonal extension, full Whittaker type, and
   actual disintegration with a positive normalization as local hypotheses.
2. `Whittaker.TwoBlockWhittakerExtensionStatement` with the two independent
   block-carrier universes `uV₁` and `uV₂`.
3. `NormalizedProductWhittakerTypeStatement` at block-carrier universe
   `max uV₁ uV₂`, which contains both actual ULift-conjugated block carriers.
4. `LowerBlockQuotientDisintegrationStatement` at field universe `uF`.
5. `InducedTailIntermediateInverseCharacterStatement` with larger tail member
   in universe `uW` and smaller tail member in universe `uV₂`.

The conclusion is the existing four-universe intermediate-tail proposition,
without alteration. It includes the literal ULift-conjugated canonical
normalized upper induction, the original character on both canonical value
sets, the supplied self-dual scalar Haar measure and its rectangular products,
and every independently supplied compatible quotient measure. This implication
asserts that the listed prerequisites suffice; it does not assert them.

The universe choices permit specializing full Whittaker type to the two lifted
block carriers and using the conditional span statement on the actual induced
carrier. The inverse-character premise applies to the canonical tail pair
`(sigma, pi2)`, in that order. The measure-transfer premise keeps its positive
scalar until the conditional Laurent-span calculation removes it.

This is a derived interface internal to the Library constructions, not a
separate statement quoted from external literature. Its rationale is the
composition of the existing five propositions: specialize full type and
extension to the canonical two-block induction, use inverse-character equality
to obtain the reversed tail integrability and continuation witnesses, specialize
actual disintegration to the intermediate lower-block chart, and apply the
conditional span input. Equality of ranks and the zero-row rectangular product
transport the result back to the unchanged canonical value sets. A proof of
this composition remains a separate contribution, and the five prerequisite
proofs remain separate from that contribution.
