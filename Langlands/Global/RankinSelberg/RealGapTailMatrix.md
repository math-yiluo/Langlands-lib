# Forward and inverse matrices of the real right tail

* `tailBlockIndex` orders the indices of the two blocks; `upperRectangle X` is the block matrix
  `(1, X; 0, 1)` and `diag(g, h)` is `(g, 0; 0, h)` in this indexing.

`RealGapTailMatrixStatement`: for `h ∈ GL_{n-k}(ℝ)`, a rectangle `X` and an orthogonal `q`,
the right tail `g = rightTail h X q` satisfies

`g = q · (1, X; 0, h)` and `g⁻¹ = (1, -X h⁻¹; 0, h⁻¹) · q⁻¹`

(in the indexing `tailBlockIndex`). `realGapTailMatrix` proves it by multiplying the displayed
block matrices.

* `tailColumns g` are the trailing `n - k` columns of `g`. `rightTail_norm_bounds`: the entrywise
  norms of `h` and `X` are at most `n` times the norm of the trailing columns of the right tail,
  and the norm of the right tail is at most `1 + ‖tailColumns‖` (orthogonal entries have absolute
  value at most one).
* `realNormalizedAbs_det_rightTail`: `|det (rightTail h X q)| = |det h|`, since orthogonal
  matrices have determinant `±1`.

This is the real counterpart of the Library's `ComplexGapTailMatrix`, used for the majorants in
the larger-gap recurrence of Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §10.1.
