# Coherence of analytification restrictions

This internal module derives the identity and composition laws for the published
affine-open analytic restriction maps from their definitions. It introduces no
source-specific mathematical claim. The field and scheme range over the same
arbitrary universe, with the complete, ultrametric, nontrivially normed field and
locally finite type hypotheses required to construct their analytifications.

`OpenGluing.restriction_refl` and `restriction_trans` establish the algebraic
restriction laws using the identity and composition laws for `Scheme.homOfLE`
and its map on global sections. They need none of the analytic hypotheses.

`OpenGluing.localMap_refl` and `localMap_trans` establish the corresponding
pointwise identities for analytic restrictions. Naturality of `pointSeminorm`
reduces both assertions to the algebraic laws. The injectivity theorem in
`AffineAnalytificationSeminormProof` then identifies the points.

`OpenGluing.RestrictionCoherence` packages precisely those two pointwise analytic
laws as a proposition. `OpenGluing.restrictionCoherence` supplies its proof. The
module is independent of the open embedding and center range arguments, so those
arguments can both import these laws.
