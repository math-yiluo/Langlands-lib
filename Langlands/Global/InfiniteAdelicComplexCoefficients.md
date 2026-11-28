# Complex coordinates of the infinite adeles

For a number field \(F\), `mixedSpaceRealAlgEquiv` identifies the actual
infinite adele ring \(F_\infty\) with the product of one copy of
\(\mathbf R\) per real place and one copy of \(\mathbf C\) per complex place.
It uses Mathlib's `InfiniteAdeleRing.ringEquiv_mixedSpace` and the real
scalar action of `realAlgebra` on the completion manifolds. At each place,
the completion embedding into \(\mathbf C\) identifies its real scalars
with the usual real inclusion. The two maps agree on rational scalars
and hence agree everywhere by continuity.

`complexifiedAdeleCoordinates` tensors this real algebra equivalence
with \(\mathbf C\) and applies `ArchimedeanGL.complexifiedScalarCoordinates`.
There is one complex coordinate for a real place and two for a complex
place. At a complex place the two coordinates use the chosen embedding
and its complex conjugate. Evaluating \(1\otimes x\) defines
`complexifiedAdeleEvaluation`, a real algebra map from \(F_\infty\) to
the complex field at each coordinate. Evaluating \(c\otimes x\)
multiplies that value by \(c\).
