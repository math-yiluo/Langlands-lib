# Covering by projective frame loci at large level

`Langlands.AbelianScheme.PolarizedFiniteLevel.FrameLocusCoverStatement` is a
proposition definition. It is a statement target only; this module proves
nothing.

## The statement

All schemes lie in one arbitrary universe `u`. For every
`P : Prerequisites.{u}` and natural numbers `g d` with `0 < g` and `0 < d`,
there is a bound `N` with the following property. Let `n ≥ N`, let `S` be a
locally noetherian scheme on which `n` is a unit, let `a : Datum P S g d n`,
and let `x` be a point of `S`. Then there is a family

`ρ : Fin (cubicProjectiveDimension g d + 2) → Fin (2*g) → ZMod n`

of `6^g·d + 1` level coefficient tuples such that `x ∈ a.frameLocus ρ`.

`Datum.frameLocus` is the projective frame locus of the internal module
`FrameLocus`. So the statement says: near every point, some `6^g·d + 1`
torsion points of the ordered full level form a projective frame of the
cubic direct image `V = π_* L³`. That is, any `6^g·d` of their evaluation
functionals form a basis of the dual of `V`.

## Why it holds

Over a locally noetherian base, `V` is locally free of rank `6^g·d` (published
`cubicDirectImage`) and commutes with base change. By the fibre criterion for
maps between locally free modules of the same rank, `x` lies in the frame locus
of `ρ` once the evaluations are a frame over the residue field `κ(x)`. Linear
independence of functionals is unchanged by field extension, so one may pass
to an algebraic closure `K` of `κ(x)`.

Over `K`, the complete linear system `|L³|` embeds the abelian variety in
`ℙ^m` with `m + 1 = 6^g·d`, and its image lies in no hyperplane. This is
Lefschetz's theorem (statement `CubicFieldEmbeddingStatement`); the
nondegeneracy is the published `Datum.cubicSectionMap_nondegenerate`. The
published `Datum.cubicSectionMap_torsionHyperplane_bound` applies the
published `CubicTorsionHyperplaneBoundStatement` (proved in the Library) to
this embedding. It bounds the number of `n`-torsion points on any hyperplane
by `6^g·d·g!·n^(2g-2)`. There are `n^(2g)` torsion points, all given by the full
level. Choose `N` with `n^2 > (6^g·d + 1)·6^g·d·g!` for `n ≥ N`. Then a
greedy choice gives a frame. First choose `m + 1` torsion points whose images
span `ℙ^m`; each new point avoids a proper linear subspace, which lies in a
hyperplane. Then choose one more point outside the `m + 1` hyperplanes spanned
by `m` of the first points.

## Provenance

This is a derived statement. It is the frame form of Mumford, Fogarty and
Kirwan, *Geometric Invariant Theory*, third edition (1994), Chapter 7 §3:
- Proposition 7.7 and its proof (printed pp.138–139, PDF pp.151–152). The
  proof shows that fewer than `n^(2g)/(m + 1)` of the `n^(2g)` points of order
  `n` lie in any hyperplane, which gives stability of the torsion
  configuration;
- Corollary 7.8 (printed p.139, PDF p.152), the bound `n > 6^g·d·√(g!)`.

Registered source
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`.
The frame selection from the hyperplane count is elementary linear algebra.
The bound `N` is not asserted to be Mumford's.

It is one of the three inputs of the internal reduction
`largeLevelChartCover_of_frameCharts` to the published
`LargeLevelChartCoverStatement`.
