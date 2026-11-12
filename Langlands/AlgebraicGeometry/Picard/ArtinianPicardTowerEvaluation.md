# Actual Artinian evaluations of the effective Picard tower bundle

This internal comparison uses the same supplied complete Noetherian local
augmented source, proper flat scheme and initial pointed stage as
`ArtinianPicardTowerAlgebraization`. Let `C` be the unchanged limiting ring
and `mC` its maximal ideal. Given any actual `ArtinianTest k K` object `A`,
an actual `k`-algebra map `α : C →ₐ[k] A.algebra` with its prescribed
augmentation equation, and a finite bound killing `mC^(a+1)`, it constructs
the actual augmented arrow `stageMap` from the selected original tower
stage to `A`. `stageMap_projection` proves that composing it with the
original limiting projection is exactly `α`.

The definition `PicardGroupoid.ArtinianPicardTowerEvaluation.evaluationIso`
identifies the formal-system evaluation with ordinary pullback of the
actual selected tower bundle along this arrow.
`effectiveEvaluationIso` gives the corresponding isomorphism for ordinary
pullback of the effective bundle along the original source map `α`.
All rings, tests and schemes stay in the same arbitrary universe `u`.

The proof checks both pullback projections to identify the finite evaluation
map followed by `adicRelativeMap` with the actual relative map of the
finite augmented factor. The quotient factorization theorem proves the
source-map equation. Ordinary line-bundle pullback composition gives the
formal evaluation isomorphism, and the existing algebraization comparison
gives the effective one.

The provenance is internal assembly of the tower, bounded adic factorization
and actual line-bundle pullback constructions. The result concerns actual
underlying bundle isomorphisms. It supplies no new residue compatibility or
coherence law for the selected tower transitions, and does not assert the full
point-fibre lifting condition or source existence needed for formal versality.
