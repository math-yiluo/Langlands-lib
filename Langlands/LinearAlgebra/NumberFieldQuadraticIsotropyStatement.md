# Local-to-global isotropy over number fields

Worker 787.

`Langlands.NumberFieldQuadraticIsotropyStatement.{u}` states that a
nondegenerate quadratic form on a finite-dimensional vector space over a
number field has a nonzero zero if its scalar extension has a nonzero zero
at every place. The types of the number field and the vector space both
belong to `Type u`, and the statement includes all finite dimensions.

The hypothesis `q.polarBilin.Nondegenerate` expresses nondegeneracy via
the polar bilinear form. The predicate `¬ q.Anisotropic` says that a vector
of value zero exists outside the zero vector, by
`QuadraticMap.not_anisotropic_iff_exists`. Each local quadratic form is the
actual `QuadraticForm.baseChange` to
`Global.placeCompletion F v`, on `Global.placeCompletion F v ⊗[F] V`.
`Global.Place F` ranges over the archimedean and finite places. The
characteristic-zero hypothesis supplies an inverse of `2 : F` for this
construction.

## Source and correspondence

John Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288,
Springer, 2021, Theorem 14.6.9 (printed p. 233) and Theorem 26.8.24
(printed p. 451). Source ID `voight-2021-quaternion-algebras`, SHA-256
`f6c56f6ca7b4bee139b88865a3cf045f899da59d0217618c4dc81daf19ef1ad4`.
The definition specializes the local-to-global implication to number fields
and nondegenerate forms. Voight writes the local form as \(Q_v\) over
\(F_v\) for each place \(v\), which here is the tensor scalar extension.

The module states the arithmetic input for the isotropy-and-cancellation
route to `Langlands.NumberFieldQuadraticIsometryStatement`. Voight derives
the isometry statement in Corollary 26.8.25 (printed p. 451).
