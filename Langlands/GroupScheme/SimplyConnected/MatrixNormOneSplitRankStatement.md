# Split rank of `SL_m(D)`

Author: Worker 165.

## Statement

`Langlands.GroupScheme.CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}`
says that over any field `K : Type u`, for any finite-dimensional central
division `K`-algebra `D : Type u` and any positive natural number `m`,

`splitRank (CentralSimpleUnits.normOne K (Matrix (Fin m) (Fin m) D))`
equals the natural number `m - 1`, coerced to `ℕ∞`.

The hypotheses are `[Field K] [DivisionRing D] [Algebra K D]
[FiniteDimensional K D] [Algebra.IsCentral K D]` and `[NeZero m]`.
Positivity of `m` ensures the matrix algebra is nontrivial and simple.
The matrix algebra inherits centrality and finite dimensionality from `D`.
Its reduced-norm-one group is the actual kernel group scheme constructed
in `Langlands.GroupScheme.CentralSimpleNormOne`. No supplied root datum,
splitting chart, maximal split torus or rank computation is a hypothesis.

The Library's `splitRank` is the supremum of the dimensions of actual
closed split subtori, with values in `ℕ∞`. Thus the assertion computes
that invariant of the group scheme; it does not define the rank by its
matrix size. Both `m = 1`, giving rank zero, and `D = K` are allowed.
There is no local-field or characteristic restriction. The universe `u`
is arbitrary. This module states the proposition and proves nothing.

## Source

J. Tits, *Classification of algebraic semisimple groups*, Proc. Sympos.
Pure Math. 9 (1966), pp. 33–62, registered as
`tits-1966-classification-algebraic-semisimple`.
Table II, explanations, printed pp. 54–55 / PDF pp. 59–60, defines `r`
as the relative rank and describes type `¹A_n` by the special linear group
`SL_{r+1}(D)` of a central division algebra `D` of degree `d`, with
`d(r+1) = n+1`. Putting `m = r+1` gives the displayed split rank `m-1`.
The degree `d` influences the absolute rank `n`, rather than this relative
rank.

The table gives a representative of each strict isogeny class. This
statement concerns precisely that special linear representative, realized
as the reduced-norm-one group of `M_m(D)`. It requires no inference that
every group of a given index is already isomorphic to this model.
The source uses rational-point notation for these representatives; the
formal assertion computes the rank of the underlying algebraic group via
the Library group-scheme model.

The table's explanation is for absolutely simple groups. For `m = 1`
and `D = K`, the model is the trivial group, and the same rank-zero
formula is the elementary degenerate case, included here to give a uniform
matrix-size statement.

## Role in the local rank-one classification

This is a focused rank computation for family (i) of
`Langlands.GroupScheme.LocalRankOneClassificationStatement`.
Once an actual group has been identified with `SL_m(D)`, the formula
forces `m = 2` when its split rank is one, giving the existing
`CentralSimpleUnits.BinaryRoot.groupScheme K D` model.
Existence of a central-simple-algebra description for an arbitrary inner
form and transport of that description to the actual group scheme
remain separate proof obligations. This proposition neither assumes nor
asserts the full rank-one classification and does not use local
Kneser–Tits.
