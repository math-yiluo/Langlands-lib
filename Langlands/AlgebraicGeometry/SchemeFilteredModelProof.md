# Proof of model descent over the original filtered rings

Worker 105 proves `InitialRingModelDescent` with
`initialRingModelDescent`, retaining arbitrary universe `u`.
This supplies the actual initial-ring specialization of the
relative Hom and prescribed-isomorphism portions of Conrad's
Theorem 3.4(1) and (3).

`initialRingModelHomColimitComparison` applies
`spectrumModelHomColimitComparison` to the actual
`initialRingAlgebraDiagram` and its cocone. The theorem
`initialRingAlgebraCoconeIsColimit` constructs its algebra-colimit
witness from the supplied original ring-colimit witness. It
preserves all three clauses and their separate finiteness hypotheses.
The original-ring spectrum formulas are definitional, so the
limiting and stage pullbacks use the exact original maps.

`initialRingModelMorphismDescent` applies `modelMorphismDescent`
to the opposite actual spectrum diagram. Its limit witness is
`spectrumConeIsLimit`, again supplied with the constructed tail
algebra-colimit witness. The first conclusion reindexes the
factorization stage by `j.unop`. The second reindexes the common
stage and the two arrows by `unop`; contravariance turns the two
cofiltered arrows into actual arrows from the given ring stages
to their common later stage. The restriction morphisms and their
equality are definitionally the ones in the target. The third
conclusion similarly reindexes the prescribed isomorphism and
retains its structural-map compatibility and exact limiting
morphism. No new isomorphism is substituted at the limit.

The final theorem conjoins the two proved assertions. The
argument uses the generic proofs and the actual tail construction;
it does not assume a tail colimit, Hom bijection or descent result
as additional data. Nonaffine and nonseparated models and
possibly noninjective ring transitions remain unrestricted.
Other morphism properties, arithmetic identifications and topology
are separate obligations.

The motivating original is Brian Conrad, *Weil and Grothendieck
approaches to adelic points*, December 31, 2011, printed pp. 5–6,
Theorem 3.4(1), Hom comparison, and (3), prescribed-isomorphism
descent and eventual uniqueness; registered source
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The small filtered-category formulation and the separate weaker
finiteness hypotheses are derived strengthenings justified by the
published generic proofs. Conrad's finitely presented models satisfy
the hypotheses for bijectivity and prescribed-isomorphism descent.

Worker 105 authored the reused Lean proof and original explanation.
Worker 706 reused that proof unchanged, checked the original source
and published dependencies, and prepared this focused proof pair
for submission. Initial-model existence, other morphism properties,
arithmetic, topology and whole-paper completion remain separate
obligations.
