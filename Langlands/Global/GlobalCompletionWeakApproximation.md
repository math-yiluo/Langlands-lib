# Weak approximation in the original global-field completions

Worker 208. This derived infrastructure supplies the finite-completion
approximation used in Conrad, *Weil and Grothendieck approaches to adelic points*
(2011), printed p.10, Example 4.3. It reuses Mathlib's general weak approximation
theorem and the published actual completion comparisons, rather than assuming
an abstract place system or replacing the completion topology.

For global function fields, `curvePlaceRealCompletionEquiv` specializes
`functionFieldAbsoluteValueCompletionEquiv` to the chosen nontrivial real
absolute value of an actual curve place. The published exact identity of the
recovered place identifies the target with the original adic completion.
The implementation transports along that identity with a private ring
equivalence; its continuity and coefficient identity follow by equality
elimination.
The comparison is continuous and preserves every original field element.
`curvePlaceWithAbsEmbedding` therefore maps the original absolute-value field
continuously and densely into that actual completion.

The actual finite diagonal `curvePlaceFiniteCompletionDiagonal` has dense range.
Distinct curve places give inequivalent absolute values because the published
absolute-value-to-place map recovers each place. Mathlib's
`AbsoluteValue.denseRange_algebraMap_pi` gives density in the finite product of
the absolute-value fields. The product of their continuous dense embeddings
into the original completions then transfers density to the displayed actual
diagonal, using its coefficient identity.

For number fields, `numberFieldFiniteCompletionDiagonal` retains every infinite
completion and any finite set of finite completions. Its dense range follows
from the published `AdelicFunctoriality.exists_algebraMap_mem_open`: a product
neighborhood contains a finite cylinder, and the interiors of its coordinate
neighborhoods are nonempty open sets to which that theorem applies.

Both arithmetic branches permit an empty finite set and arbitrary common
universe. The function-field branch assumes finite constants and a finite
extension of the specified rational-function field with compatible scalar
tower, imposing no separability restriction. This module supplies arithmetic
coefficient approximation; projective-point density and its nonclosedness and
nondiscreteness consequences remain separate obligations.
