# Completeness and cocompleteness of original nondegenerate modules

This module reuses Worker 6's shared Lean proof and explanation; Worker 695
prepared the exact-target submission. It implements the first assertion of
the Proposition of Renard I.6,
printed pp.27–28 / PDF pp.33–34 of the French edition dated 9 July 2026.
The governing source is registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original passage was read. This file proves the four targets of
`NondegenerateModuleCompletenessStatements` using the original module
category and its published abelian data.

The proof imports the published statement and dependency pairs by their
Lean names and leaves them unchanged.

The theorem `complete` uses the actual fan whose vertex is the
nondegenerate part of the coordinate product and whose maps are the
original coordinate projections. Its universal lift assembles the
original maps into a tuple. A fixing idempotent for each source vector
fixes all its image coordinates simultaneously, so the tuple belongs to
the actual nondegenerate part. The construction's `fanIsLimit` proves
the required universal property. Mathlib's
`hasProducts_of_limit_fans` converts these explicit fans into the source
completeness predicate.

The theorem `cocomplete` uses the published finite-support direct sum,
its actual singleton maps and `cofanIsColimit`. Nondegeneracy is proved
with common upper idempotents for finite-support vectors, and the
universal map is finite-support additive descent on the original
intertwiners. Mathlib's `hasCoproducts_of_colimit_cofans` packages these
cofans as the source cocompleteness predicate.

For `allLimits`, the named actual abelian category supplies equalizers.
The published theorem `Langlands.Renard.sourceCompleteHasLimits` combines
these with `complete` to give every limit of a diagram of the specified
size. Its underlying Mathlib construction uses an equalizer between
products. Dually `allColimits` combines actual coproducts and abelian
coequalizers via `sourceCocompleteHasColimits`.
`completenessAssertions` is exactly the conjunction of the four results.
This is the route described in I.6 and the published Appendix A.VI.2(10)
proof. It introduces no assumed product or colimit replacement.

The coefficient, index and residual carrier universes are independent.
The category carrier universe is `max uI uM`; its arrows are the actual
original additive intertwiners. The argument uses only a nonunital ring
with finite local units, additive module actions and nondegeneracy.
The source's complex-algebra case is a specialization. There is no
finite-dimensional, finite-generation, unital-action or nonempty-index
assumption. Examples retain the full targets and test unequal universes.

AB5, local finite type (the source's AB6) and filtered-colimit exactness
are separate I.6 obligations. They are not asserted by this proof.
