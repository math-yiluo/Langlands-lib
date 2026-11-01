# Completeness and cocompleteness of the original nondegenerate category

This statement module covers the first assertion of the Proposition in
Renard I.6, printed pp.27–28 / PDF33–34 of the French edition dated
9 July 2026. The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passage was read. Its first assertion is completeness and
cocompleteness; the proof explains this by existence of arbitrary products
and direct sums and then of arbitrary limits and colimits. The remaining
assertions about AB5, the source's AB6 (local finite type), and
filtered-colimit exactness are separate obligations. The source explicitly
distinguishes its AB6 from Grothendieck's AB6 in footnote 3 on printed p.28.

All statements use the published actual category
`NondegenerateModuleCat A`, whose morphisms are original additive
intertwiners. `A : Type uA` is an arbitrary nonunital ring satisfying
`hA : IsIdempotented A`. The source uses complex idempotented algebras,
and the stated arbitrary-ring extension is derived from the
coefficient-independent constructions. A vector in the direct sum has finite
support; a common upper bound of the finitely many fixing idempotents fixes
that vector. The coordinatewise ambient product has a nondegenerate part
consisting of the tuples fixed by one idempotent in every coordinate.
An original additive intertwiner from a nondegenerate module factors into
this part, since an idempotent fixing a source vector fixes its image.
These constructions need only the ring and original-action hypotheses.
There is no field, unit-action, nontriviality, finite-generation or
finite-dimensional restriction.

`CompleteStatement` asserts the published source predicate
`Langlands.Renard.IsSourceComplete.{uI}` for this category, using the
published named abelian data
`NondegenerateModuleCat.abelian A hA`. This predicate means existence of
every `uI`-indexed product, with no exactness clause.
`CocompleteStatement` analogously uses `IsSourceCocomplete.{uI}`, which
means existence of every `uI`-indexed coproduct. These are the source's
conventions, as specified in Appendix A.VI.2, printed p.263 / PDF p.269,
and exposed by the unchanged public `RenardGrothendieckAxioms` interface.

`AllLimitsStatement` asserts Mathlib's `HasLimitsOfSize.{uI,uI}`.
`AllColimitsStatement` asserts `HasColimitsOfSize.{uI,uI}`.
Thus diagrams are actual functors `J ⥤ NondegenerateModuleCat A`, with
`J : Type uI` and `Category.{uI} J`. The conclusions require their actual
categorical limits and colimits. They assume neither a replacement
category nor any limit or colimit structure. They also have no extra
finite, discrete, filtered or nonempty restriction on the diagrams.

`CompletenessAssertions` is exactly the conjunction of these four
statements. Every declaration is a closed Prop-valued definition.
The coefficient, index-size and residual carrier universes `uA,uI,uM`
are independent. The module carrier universe is `max uI uM`, so actual
products and finite-support sums fit into the category. Taking `uI = uM`
gives all diagrams at the carrier size. The statements do not claim
products indexed above the explicit carrier bound. Their complete bodies
are checked by reflexive unfolding examples. Closed interfaces and all six
permutations of three distinct universe levels are checked in the module.
These examples verify the interfaces; they do not prove the assertions.

The intended proof uses the actual coordinate product restricted
to its nondegenerate part, and the actual finite-support direct sum. The
product requires a single idempotent fixing the entire tuple; a map from
a nondegenerate source has this property by equivariance.
The published general theorems `Langlands.Renard.sourceCompleteHasLimits`
and `sourceCocompleteHasColimits` then give the all-diagram conclusions
using the actual abelian category. This module supplies statements only,
and neither that route nor compilation constitutes an accepted proof.

The previously read supplementary 2010-edition corrections do not replace
the governing 2026 source. The supplement is registered as
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`;
PDF pp.1–2 and 18–19 were consulted for this unit.
