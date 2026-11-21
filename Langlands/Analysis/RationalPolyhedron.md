# Finite rational polyhedra in real coordinates

`Langlands.rationalPolyhedron A b` is the subset of `n → ℝ` defined by
`A x ≤ b`, componentwise, for a rational matrix `A : Matrix m n ℚ` and a
rational right-hand side `b : m → ℚ`. Both are cast to `ℝ` in the
inequalities. The coordinate type `n` is finite. Closedness and convexity
hold for any row type `m`; the extreme-point and maximum results require a
finite row type. No full-dimensionality, irredundancy, or rationality of
the objective is required.

## Rationality of extreme points

`exists_ratCast_eq_of_mem_extremePoints_rationalPolyhedron` proves that any
extreme point `x` has all coordinates in the image of `ℚ → ℝ` by finding
one vector `q : n → ℚ` whose coordinatewise cast equals `x`.

1. Take the rows tight at `x`, obtaining a matrix `K` over `ℝ`. If two
   vectors have equal image under `K`, their difference `d` lies in its
   kernel. Every tight inequality remains an equality at `x ± r d`.
   Every other inequality holds for all sufficiently small `r` because
   it is strict at `x` and the row value depends continuously on `r`.
   There are finitely many inequalities, so one `r > 0` works for all.
   The two resulting points lie in the polyhedron and their open segment
   contains `x`. Extremality forces `r d = 0`, hence `d = 0`. Thus `K` is
   injective on vectors.
2. The tight matrix is the real cast of a rational matrix `C`. The real
   Gram matrix of the columns is the cast of `Cᵀ C`; its kernel agrees
   with that of `K`. Its determinant is therefore nonzero, and the
   determinant of `Cᵀ C` over `ℚ` is nonzero as well. Solve the rational
   square system `Cᵀ C q = Cᵀ c`, where `c` is the tight right-hand side.
   After casting to `ℝ`, both `q` and `x` solve this same square system.
   Injectivity gives equality.

## Maximization

`exists_ratCast_isMaxOn_rationalPolyhedron` takes a nonempty compact
`rationalPolyhedron A b` and a continuous real linear functional on the
coordinate space. It first obtains a maximizer by compactness. The
nonempty exposed face of maximizers is compact. The finite-dimensional
Krein–Milman result gives an extreme point of that face, which is extreme
in the original polyhedron as well. The preceding rationality result
provides a rational vector attaining the same maximum. This is an existence
result, not a vertex enumeration or a simplex algorithm.

## Provenance and consumer

This internal construction supplies the finite-polyhedron step for the
rational max–min argument after Kaletha–Prasad Definition 13.4.2,
*Bruhat–Tits Theory: A New Approach* (2023), printed pp. 472–473 / PDF
pp. 503–504. In that argument each cell where a given affine root realizes
the minimum is cut out by finitely many rational affine inequalities in
rational coordinates. The book invokes rational vertices and attainment at
one of them in this setting; the construction above derives the general
coordinate statements using Mathlib's matrix and convexity API. It does
not formalize affine root coordinates or the optimal-point conclusion.
The authors' 1 November 2024 corrections do not alter §13.4 (Chapter 13,
PDF p. 49). No external code is adapted.
