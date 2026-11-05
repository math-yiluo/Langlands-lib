# Proof of closed-immersion descent over the original ring system

Worker 105 authored this proof, reused here by Worker 1596.

`ringSystemClosedImmersionDescent` proves exactly
`Langlands.AlgebraicGeometry.SchemeLimitModel.RingSystemClosedImmersionDescent`.
The statement's paired Markdown records the source and all hypotheses.

`spectrumClosedImmersionDescent` applies the proved
`relativeClosedImmersionDescent` to the actual spectrum diagram,
compatible structure maps and spectrum cone. `spectrumConeIsLimit`
constructs the limit witness from the algebra-colimit witness, and
`spectrumCone_compat` supplies the exact structure-map equations.
The existential stage is reindexed from the opposite category to the
original algebra diagram by taking unop, and conversely op.

`initialRingClosedImmersionDescent` applies that result to the actual
initial-stage algebra diagram and cocone. Its colimit witness is
`initialRingAlgebraCoconeIsColimit`, derived from the original ring
colimit. The published spectrum-map formulas are definitionally the
original cocone map and original transition map, giving the exact
proposition without any assumed ring comparison.

`finitePresentationInitialRingClosedImmersionDescent` derives the
relative hypotheses from the source model hypotheses. Rewrite the
composite `f.left ≫ Y.hom` as `X.hom`. Local finite presentation of
`X.hom` implies local finite type of that composite, and
`locallyOfFiniteType_of_comp` gives local finite type of `f.left`.
`QuasiCompact.of_comp` and `QuasiSeparated.of_comp` give the remaining
relative properties using the model finiteness assumptions. Apply the
proved initial-ring result. The final theorem conjoins all three forms.
The proof uses arbitrary nonaffine and nonseparated models and permits
noninjective ring transitions. Other source clauses remain separate.
