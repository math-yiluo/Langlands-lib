# Split real test arguments under leading determinant normalization

This module is the real counterpart of the Library's `ComplexGapNormalizationColumns`, with the same
statement over `ℝ`.

* `leadingSide_mul`, `leadingSide_involutive`: `leadingSide dual` is multiplicative and an involution.
* `leadingSide_mul_stack`: `(leadingSide (B · diag(g, 1))) · leadingStack (leadingSide h) Y =
  (leadingSide B) · leadingStack (leadingSide (g h)) Y`.
* `triangularFourier_right_rankInclusion`: `triangularFourier k q a (B · diag(g, 1)) Ξ Z =
  triangularFourier k q a B Ξ Z`, because the earlier Fourier columns are supported in the tail.
* `tailEndpoints_right_rankInclusion`: right multiplication by `diag(g, 1)` fixes the first tail column
  and the last row of the inverse.

`RealGapNormalizationColumnsStatement` (proved by `realGapNormalizationColumns`) collects these four
identities. The proofs use the block form of `rankInclusion` and its action on columns supported in the
tail and on stacked columns.

This is an internal step of the convergence and Mellin analysis of the larger-gap recurrence in Jacquet, *Archimedean Rankin–Selberg integrals* (2009), §10.
