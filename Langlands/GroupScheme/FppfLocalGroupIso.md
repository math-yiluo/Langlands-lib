# Descent of local group isomorphisms on fppf covers

This derived module extends the descent construction in
`Langlands.GroupScheme.LocalGroupIso` to covers whose structure morphism is
flat, surjective and locally of finite presentation. In particular it applies
to the étale surjective covers in the relative quasi-split inner-form targets,
without requiring those covers to be quasi-compact.

For a natural family `e : LocalGroupHom G H U` that is independent of its
cover point, `LocalGroupHom.valueFppf` descends the local value at each group
point. Pulling `U` back to a test scheme gives an effective epimorphism,
by the fppf descent instance in Mathlib. Two local values over points with
the same image agree by independence and naturality. The effective
epimorphism therefore descends the underlying morphism; cancellation by
its epimorphism property verifies that this morphism lies over the base.

The lemmas `valueFppf_fac`, `comp_valueFppf` and `valueFppf_naturality`
verify recovery and naturality of these descended values. The definition
`pointsHomFppf` proves that the values preserve the group operations by
checking after the same effective epimorphism. `descendFppf` applies the
existing `homOfPoints` construction to give a group-scheme homomorphism.

For `e : LocalGroupIso G H U`, `LocalGroupIso.descendFppf` applies that
homomorphism construction to `e` and its inverse. Their composites are
identities because they are identities after pullback to the cover.
`descendOfTrivialFppf` first corrects the local isomorphisms using a
cochain whose coboundary is the supplied discrepancy cocycle. The
existing `twist_isIndependent` theorem makes them independent, and then
`descendFppf` descends them.

Finally `descendOfTrivialInnerCocycleFppf` uses the existing construction
of the natural inner-discrepancy cocycle from a faithful action and
pointwise innerness. Triviality of that constructed cocycle is an explicit
hypothesis. The result is an actual isomorphism `G ≅ H` on the original
base. This module proves neither cocycle vanishing nor existence of
quasi-split inner forms.

The proof is an internal adaptation of the published fpqc descent proof
in `LocalGroupIso`: effective epimorphy of every pulled-back cover is
supplied by flatness, surjectivity and local finite presentation in place
of flatness, surjectivity and quasi-compactness. The original module and
its hypotheses remain unchanged.
