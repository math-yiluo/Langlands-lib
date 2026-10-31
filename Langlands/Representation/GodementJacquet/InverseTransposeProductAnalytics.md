# Inverse-transpose analytics for product induction

This internal module composes two published geometric constructions and then
applies `CoefficientTransport` to the actual coefficient families. It supplies
a representation and analytic-predicate bridge, without assuming either
analytic predicate holds.

For a p-adic field with the supplied topological data `T`, any block shape
`B`, dependent complex carrier family `V`, and smooth factor actions `σ`,
`inverseTransposeProductReversalEquiv` constructs an equivalence from the
inverse-transpose pullback of `T.normalizedProductInduced B σ` to the normalized
upper induction for `B.reverse` with factors
`(σ i.rev).comp (inverseTranspose (B.size i.rev) F.Carrier)`.
The target carrier family is the actual dependent family `i ↦ V i.rev`,
with its inherited additive and module structures. Both field and carrier
universes are independent.

The first equivalence is the published
`TopologicalData.inverseTransposeProductToOppositeEquiv` from
`Induction.InverseTranspose`. It carries upper induction with the pulled-back
ambient action to normalized opposite induction of the pulled-back factors,
including the parabolic and half-modulus change. The second is the
equivalence supplied by the published `glOppositeProductReversal`. The factors
required by that theorem are smooth because inverse transpose is continuous.
The theorem reverses the full ordered block family and reindexes its tensor
carrier; its published modulus calculation supplies the normalization.
The implemented map is the composition of these two equivalences. This module
does not reconstruct or alter either geometric construction.

At actual rank `r + 1`, `iotaMatrixAnalyticAssertions_product_iff` first applies
the coefficient transport theorem identifying the transformed predicate with
the ordinary predicate for the inverse-transpose pullback. It then transports
the ordinary predicate across the constructed equivalence. The common
convergence bound, all tests and actual bi-smooth coefficients, rational-value
family, Laurent-span generator, and exactly the supplied group measure and
polynomial are retained.

These are derived internal results using existing induction geometry. Their
purpose is to justify the transformed branch of the conditional two-block
Godement–Jacquet theorem without any contragredient identification for
reducible representations. The module proves no convergence, rationality,
finite product expansion, reverse generation, or Fourier functional equation.
It works for every block shape to which the published geometry applies,
including the positive two-block shape needed by that theorem.
