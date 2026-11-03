# Comparing closed schematically dominant group factorizations

This internal adapter compares actual closed image factorizations, over an
arbitrary base scheme and in universe `u`. It uses the published closed
containment lemma from `Rational/TorusCentralizerImage`, the uniqueness
isomorphism for represented subgroup functors, and Mathlib's flat-base-change
theorem for quasi-compact schematic dominance.

`isSchemeTheoreticallyDominant_baseChange b f` preserves schematic
dominance of a quasi-compact group-scheme homomorphism under a flat base
change. The proof identifies the underlying scheme morphism of the
group-scheme base change as a pullback of the original morphism and applies
the scheme-level theorem.

For two factorizations `p ≫ i = q ≫ j` with a common source and target,
suppose the underlying scheme maps of `p` and `q` are schematically
dominant and `i` and `j` are closed subgroup inclusions. The theorem
`SchematicImage.range_eq_of_dominantFactorizations` identifies their
subgroup functors on every test scheme. It descends each containment along
the corresponding dominant factor. No quasi-compactness or flatness
assumption is needed for this comparison.

`SchematicImage.isoOfDominantFactorizations` constructs the resulting
isomorphism of the two actual intermediate group schemes. Its
`_hom_comp` theorem states compatibility with the specified inclusions.
The construction is the existing uniqueness isomorphism for two
representatives of one subgroup functor.

There is no smoothness, reducedness, connectedness, affineness, field or
torus hypothesis in the comparison theorem. The base-change lemma alone
uses flatness and quasi-compactness. This module supplies image comparison
infrastructure; it does not assert the nonsplit torus-image theorem.
