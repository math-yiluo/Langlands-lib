# Diagonal weights for the original Tits data at a finite stage

Internal infrastructure for `SpecialLinearTitsCocycleStatement`, combining the
finite-stage root-restriction comparison, the coordinate pinned isomorphism,
and the finite-to-pivot diagonal-torus bridge. No new literature assertion is
introduced.

`stageDiagonalMap d d' t c` maps the scalar extension of the original maximal
split torus to the published last-pivot diagonal coordinate torus. It first
applies the scalar extension of `stageTorusMap`, then the inverse torus
isomorphism of the coordinate pinning, and finally `lastPivotTorusIso`.
`stageDiagonalWeight` descends each diagonal character through the inverse of
the canonical split-torus character base-change equivalence.

`rootRestriction_stageDiagonalWeight_sub` assumes that the root-datum
equivalence of the stage has the actual tower character map as its weight map.
It identifies the original restriction of the corresponding stage simple root
with the difference of two adjacent descended weights. The proof uses the
finite-stage root-restriction formula, the coordinate pinning's simple-root
pullback formula, and the equality of finite root characters with the pullback
of last-pivot diagonal-weight differences. Injectivity of character base change
then gives the equality over the original field. If the stage numbering matches
the prescribed numbering of the original vertices,
`numbered_rootRestriction_stageDiagonalWeight_sub` yields the exact
simple-root clause of the target statement.

When the identification of the original and stage tori respects their ambient
inclusions, `stageDiagonalMap_factorization` proves that base change of the
original split inclusion followed by the inverse coordinate pinned group
isomorphism equals the resulting diagonal-torus inclusion. It applies base
change to `stageTorusMap_square`, uses the inverse pinning square, and replaces
the finite diagonal inclusion by the last-pivot one.

`diagonal_stageDiagonalWeight` assumes an actual local group isomorphism whose
base-change isomorphism is the standard special-linear model comparison
followed by the coordinate pinned group isomorphism. Cancellation identifies
its inverse with the inverse pinned group isomorphism after the model
comparison. The preceding factorization and
`diagonal_of_baseChangeFactorization` then give the diagonal matrix formula
for every original relative test and every cover point.

The universe, fields, characteristics, and natural rank are unrestricted,
including ranks zero and one. The root comparison uses a specified embedding
tower into the separable closure. The diagonal factorization needs only the
inclusion square and the displayed local-isomorphism equation. This module
does not construct the finite Galois field or the local isomorphism, and makes
no Galois discrepancy assertion. The coordinate-pinning construction is due to
Worker 243, using coordinate root data by Worker 235 and Cartan extension by
Worker 237; the finite-stage interfaces originate with Workers 61 and 5375.
