# The two-irreducible-quotient criterion for a strong head

Author: Worker 341.

This proof module proves the published `HeadQuotientCriterionStatement` in
`Langlands.Classification`, with independent group universe `uG` and carrier
universe `uV`. Its aggregate theorem is `headQuotientCriterion`; the two component
theorems are `unequalIrreducibleQuotientKernels` and
`irreducibleHeadProductCriterion`. Each theorem has exactly its corresponding
published proposition as its complete type, with no term parameters.

For two surjective irreducible quotient maps, the proof uses the published
`isIrreducible_iff_isCoatom_ker` to identify their subrepresentation kernels as
maximal. Equality of those kernels would imply equality of their underlying
linear kernels. Thus distinct linear kernels yield distinct maximal
subrepresentations, whose supremum is the whole representation by
`IsCoatom.sup_eq_top_of_ne`. The proof transfers this equality to submodules.
To lift a pair `(w₁,w₂)`, it chooses `x` above `w₁` and `z` above
`w₂ - q₂ x`, writes `z = a + b` with `a` in the first kernel and `b` in the
second, and verifies that `x + a` maps to the desired pair under Mathlib's
actual intertwiner `q₁.prod q₂`.

For the forward implication of the head criterion, the witnessing head map
supplies the required irreducible quotient. A hypothetical surjection onto a
product gives two surjective quotient maps by composition with the actual
projection intertwiners. Head uniqueness makes their linear kernels equal.
Irreducibility of the first factor supplies a nonzero vector `w`; a lift of
`(w,0)` belongs to the second projection kernel and cannot belong to the first,
contradicting that equality.

Conversely, the proof chooses an irreducible quotient using the existence
conjunct. Any other irreducible quotient map with a different kernel would, by
the first component theorem, give a forbidden surjection onto the product.
All irreducible quotient maps therefore have the same kernel, exactly the
published `IsIrreducibleHead` condition.

The provenance is an internal algebraic deduction from the published
[statement](HeadQuotientCriterionStatement.md),
[constituent relations](ConstituentRelations.md),
[canonical head definitions](CanonicalConstituents.md), and the maximal-kernel
lemma in [Cosocle](Cosocle.md), using Mathlib's lattice and linear-map operations.
No external literature claim is used. The proof needs no finite length,
finite dimension, smoothness, admissibility, topology, or classification
hypothesis. Both product factors can be the same representation, and existence
of an irreducible quotient remains an explicit conjunct. All carriers use
`Type uV`, independently of `G : Type uG`. No imported Lean or Markdown pair is
modified.
