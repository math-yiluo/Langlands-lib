# Rational points of the glued scheme analytification

`Langlands.Analytic.SchemeAnalytification.schemeAnalytificationRationalPoints`
proves the unchanged published proposition
`SchemeAnalytificationRationalPointsStatement.{u}` in every universe. For every
complete, ultrametric, nontrivially normed field `K` and scheme morphism
`f : X ⟶ Spec K` locally of finite type, it establishes chart independence,
injectivity, the union formula for the rational image, and the topological
embedding of actual relative scheme points for
`schemePointTopology K (Over.mk f) K`.

The proof supplies the three inputs of
`RationalPointsComparison.isEmbedding_analyticRationalPoint`.
`AffineAnalytification.affineAnalytificationRationalPointNaturality.{u,u,u}`
supplies naturality under restriction of coordinate algebras. The embedding
clause of `AffineAnalytification.affineAnalytificationRationalPoints` supplies
the affine rational-point embedding. Finally,
`OpenGluing.isOpenEmbedding_ι K f U` supplies the open embedding of each affine
analytic chart into the quotient `Space K f`.

The imported rational-point reduction uses common affine refinements to prove
chart independence and the union formula. It calculates rational centers
directly from the evaluation seminorms. When an analytic rational point lies
in the chart for `U`, the rational-center identity places the image of the
closed point of `Spec K` in `U`. This gives the factorization through `U`
required by Mathlib's local embedding criterion. Together with the affine
embeddings and the coinduced definition of the scheme-point topology, this
criterion proves the global embedding. The theorem takes its injectivity from
this embedding and assembles the four clauses in the order of the published
statement.

This is an internal assembly of the existing comparison constructions and
proofs. The implemented reduction adapts a direct rational-center
calculation written for the proof of `AnalytificationCenterStatement`. The
contextual literature and its scope are recorded in the
unchanged statement's paired Markdown.
