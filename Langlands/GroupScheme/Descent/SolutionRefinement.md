# Restriction of supplied actual descent solutions

This internal construction combines `Descent.Refinement` with the actual
commuting-square comparison from `Descent.SquareSemilinear`. All schemes lie
in one arbitrary universe. None of the maps requires covering, flatness,
affineness, reducedness or quasi-compactness assumptions.

Let `D : Datum p G`, with `p : S → B`, and suppose that `s : Solution D` is
already supplied. Given a commutative square `q ≫ p = t ≫ b`, where
`q : V → S`, `t : V → C` and `b : C → B`, `Solution.reindex` supplies an
actual solution of `D.reindex t q b w`. Its group over `C` is the pullback
of `s.obj` along `b`. Its isomorphism over `V` first uses
`squareComparison b t p q w.symm s.obj` to compare the two iterated
pullbacks and then the pullback along `q` of the original `s.iso`.

The compatibility proof has two parts. `squareComparison_compatible` shows
that the actual square comparison respects the canonical datum on the
pullback along `b` and the reindexed canonical datum on the original
pullback along `p`. The implementation cancels the comparison that collapses
the target pullback tower, invokes `hom_ext_pullback_tower`, and compares
projections to the original group. `canonicalDatum_transition_fst` and
`canonicalDatum_reindexOverlap_fst` provide the required projection formulas
for original canonical transitions and the restricted canonical overlap.
They follow from the published canonical-overlap projection formula and the
direct-pullback comparison formulas. This argument proves equality of actual
scheme morphisms.

For the second part, `Compatible.reindex` pulls back the original
`s.compatible`. Composing these two compatible homomorphisms verifies the
constructed solution comparison.

`Solution.refine` specializes the square to the cover `q ≫ p` over the
original base. As defined through `reindex`, its descended object is the
pullback of `s.obj` along the identity of `B`, canonically isomorphic to
`s.obj`. `Solution.baseChange` specializes to the two projections of the
scheme pullback of `p` along any map `b`.

These constructors restrict an existing actual solution. They require that
solution as input and do not establish effective object descent from a
datum alone, or prove the quasi-split inner-form existence statement.
