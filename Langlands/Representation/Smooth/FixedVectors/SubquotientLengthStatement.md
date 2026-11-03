# Compact-open subquotient detection and length reduction

Worker 1210. Worker 189 contributed the requested interface and its use in the
Howe finite-length implication.

These are internal proposition targets derived from the published
`Langlands.Compact.fixedVectorSurjectivity` and the elementary fixed-vector
strict-chain argument. They do not assert the reductive-group detection
theorem. Their source context is the fixed-vector filtration argument of
Renard VI.6.3, French version dated 9 July 2026, printed pages 178–179 /
PDF pages 184–185, registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The general topological-group assertions here are internal reductions of that
argument, rather than assertions attributed verbatim to the source.

Both assertions concern an arbitrary topological group, a smooth complex
representation on a carrier in an independent universe, and a specified compact
open subgroup `K`. No topology on the representation carrier is assumed.
For actual subrepresentations `S < T`,
`Langlands.LengthCriterionProof.quotientRep S T` is the action induced on the
actual quotient of `T.toSubmodule` by the inverse image of `S.toSubmodule`
under the inclusion of `T` in the ambient carrier. Because `S ≤ T`, this is
the usual successive subquotient `T/S`.

`CompactOpenSubquotientFixedVectorStatement` says that if this quotient's
`K`-fixed subspace is nontrivial, there is an ambient vector that lies in `T`,
is fixed by `K`, and lies outside `S`. Compact-open exactness supplies a lift
fixed by `K` inside `T`. A lift of a nonzero quotient vector cannot belong to
`S`. The assertion does not require admissibility or finite dimension.

`CompactOpenSubquotientLengthStatement` assumes that the ambient `K`-fixed
space is finite dimensional and that every strict successive subquotient
has nontrivial `K`-fixed vectors. Its conclusions are actual composition
length at most the dimension of the ambient fixed-vector space, using
`Langlands.HasCompositionLengthAtMost`, and actual finite length of
`ρ.asModule` over `MonoidAlgebra ℂ G`. The zero representation is included.

`CompactOpenSubquotientLengthReductionStatement` is exactly the conjunction
of these two assertions, with independent group and carrier universes.
There is no proof in this statement module.

The existence of a compact open subgroup detecting all strict subquotients of
the reductive rational-point representation remains an obligation. Neither this
conditional reduction nor its dimension bound proves the unrestricted
`RationalPointsFinitelyGeneratedAdmissibleFiniteLengthStatement`, the separate
converse, the VI.6.3 intermediate assertions, or the stronger source bound for
its specially chosen compact subgroup.
