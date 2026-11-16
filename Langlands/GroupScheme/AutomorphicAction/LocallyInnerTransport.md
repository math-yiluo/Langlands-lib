# Transport and composition of fppf-locally inner automorphisms

Worker 561.

This internal module develops the formal calculus for the local-innerness
predicate defined in `AutomorphicAction.LocallyInner`. It is intended for the
comparison of pinned models; it does not prove existence of a pinned
normalization.

For any automorphic action, the identity point represents the identity
automorphism, an inverse point represents the inverse automorphism, and the
product of two representing points in action order represents composition.
For conjugation these statements give local innerness of the identity and
closure under inverses. Composition uses the scheme pullback of the two
supplied fppf covers as a common fppf refinement, and multiplies the refined
conjugators in action order.

Transport through an actual group-scheme isomorphism carries a local
conjugator to its image under that isomorphism. This proves preservation of
local innerness without assuming any geometric property of either group.
All bases and test schemes are arbitrary. The results are derived from
the published group-scheme point calculus and fppf pullback properties.

For an arbitrary map of bases, `IsFppfLocallyInner.baseChange` pulls back
the witness cover and lifts its conjugator by `baseChangePointsEquiv`.
Flatness, surjectivity and local finite presentation are preserved by this
pullback. The multiplicative point equivalence, its naturality in the test
scheme, and its compatibility with the pulled-back automorphism prove the
conjugation equation on every refinement of the new cover.

The Prop-valued definition `IsFppfInnerEquivalent e d` says precisely that
`e ≪≫ d.symm` is fppf-locally inner. Here `e` and `d` are actual isomorphisms
with the same source and target, and the discrepancy is an automorphism
of their source. The module proves reflexivity, symmetry, transitivity,
compatibility with precomposition and postcomposition by actual
isomorphisms, compatibility with composition in both variables, inversion
of both comparisons, and arbitrary base change.

These are internal consequences of the local-innerness definition, the
group laws for conjugation, and the scheme pullback adjunction. They do
not assert existence or uniqueness of any normalized pinned comparison,
or prove `RelativePinnedComparisonExistenceStatement`.
