# Proof of affineness descent over the original ring system

Worker 105 proves `RingSystemAffinenessDescent` with
`ringSystemAffinenessDescent`, retaining the arbitrary common universe
`u` and all three clauses of the target. This supplies the actual-ring
specializations of the affineness clause of Conrad's Theorem 3.4(2),
printed pp. 5–6.

`spectrumAffinenessDescent` applies the generic
`relativeAffinenessDescent` to the published actual spectrum diagram,
its structural natural transformation and its cone. The
`spectrumConeIsLimit` witness is constructed from the supplied algebra
colimit witness. `spectrumCone_compat` supplies the required equality
of structural maps. Reindexing the existential stage by the opposite
category gives a stage in the original algebra category.

`initialRingAffinenessDescent` applies this result to the actual
`initialRingAlgebraDiagram` and `initialRingAlgebraCocone`. The witness
`initialRingAlgebraCoconeIsColimit` derives its algebra-colimit property
from the original ring-colimit witness. The spectrum structural maps
and limiting base map are definitionally the original spectrum maps,
so the result has the exact target type without transporting either
model or replacing any transition map.

For `finitePresentationInitialRingAffinenessDescent`, the equation
`Over.w f` identifies `f.left ≫ Y.hom` with `X.hom`.
`QuasiCompact.of_comp` uses quasi-compactness of this composite and
quasi-separatedness of `Y.hom` to establish quasi-compactness of `f`.
`QuasiSeparated.of_comp` establishes quasi-separatedness of `f` from
that of the composite. The preceding initial-stage result then
applies. Local finite presentation is retained as part of the
source's finite-presentation specialization, while the stronger
preceding form needs only these derived relative finiteness properties.

The final theorem conjoins the three proved clauses. Nonaffine and
nonseparated models and noninjective transitions are retained.
The proof does not assert the other morphism properties or any
arithmetic or topological consequence.
