# Split-solvable fixed points on pseudo-complete schemes

The theorem
`Langlands.GroupScheme.splitSolvablePseudoCompleteFixedPoint.{u}` proves exactly
the published
`Langlands.GroupScheme.SplitSolvablePseudoCompleteFixedPointStatement.{u}`.
For every field `k`, a split-solvable group scheme `H` acting on a
pseudo-complete `k`-scheme `X` with a `k`-rational point has a `k`-rational
point fixed on every relative scheme test and refinement. The field and
schemes lie in arbitrary universe `u`; the theorem imposes no characteristic,
perfection, algebraic-closedness or reducedness condition.

The statement is the formal version of Conrad–Gabber–Prasad,
*Pseudo-reductive groups*, second edition (2015), Proposition C.1.5,
printed pp.585–586 (one-based PDF pp.611–612), registered as
`conrad-gabber-prasad-2015-pseudo-reductive`, SHA256
`1b77af44c90211db9a3efa50896a3722f4fd2df332b7ce2ec52202eb243e7f54`.
The implementation uses induction on the actual normal series in the
published split-solvability predicate. For the elementary step it uses
equivariant orbit descent followed by a local power-series argument,
as implemented in `SchemeActionOrbitDescent` and `ElementaryOrbitLimit`.
This differs from the source's fixed-locus and projective-line route.

`SchemeAction.isFixed_of_range_id_eq_bot` handles a group whose identity
range is the bottom subgroup functor. Every group point on every test is
in that range and therefore equals the identity. The action unit law
makes every point fixed in the full `SchemeAction.IsFixed` sense.

`SplitSolvable.exists_isFixed_of_hasSeries` proves a stronger intermediate
result: an affine group with a supplied finite `HasSeries` fixes a
rational point of any pseudo-complete scheme that has a rational point.
It inducts on the length of the supplied series:

1. Length zero is the preceding trivial-group lemma.
2. At a successor, the series supplies a closed subgroup `j : N ⟶ H`,
   an elementary group `V`, a represented fppf quotient `q : H ⟶ V`
   with full kernel range equal to the range of `j`, and a shorter series
   for `N`. Closedness of `j` and affineness of `H` make `N` affine.
   Apply induction to the restriction of the action along `j`, obtaining
   a rational point `xN` fixed by `N` on all tests.
3. `SchemeAction.quasiCompact_quotient` makes `q` quasi-compact from
   affineness of `H`. Together with the flatness and surjectivity
   supplied by the fppf quotient, this permits
   `SchemeAction.exists_orbitMap_factor` to descend the orbit of `xN`
   to an actual morphism `ρ : V.X ⟶ X`.
   `SchemeAction.equivariant_of_orbitMap_factor` proves
   `a.act h (v ≫ ρ) = ((h ≫ q.hom.hom) * v) ≫ ρ`
   for all relative tests `T` and all points `h` and `v` over `T`.
4. `SchemeAction.exists_isFixed_of_elementary_equivariant` produces
   the required all-test fixed rational point from `ρ`. That theorem
   constructs its valuative extension from `IsPseudoComplete` and
   proves fixedness using power-series substitutions for Ga and Gm,
   injectivity of power-series localization and separatedness.

The final theorem obtains the finite series and affineness from the
unchanged `IsSplitSolvableGroupScheme H` predicate and extracts the
initial point from the statement's `Nonempty` premise. It then applies
the finite-series theorem. The stronger intermediate result does not
need the other outer fields of split solvability; the exact final
theorem still takes the full published predicate.

Every quotient and orbit morphism used here is constructed from the
series and action. The proof adds no geometric existence premise to
the target and retains actual categorical actions and the complete
fixedness predicate, including possibly nonreduced targets and tests.

Worker 1439 implemented the induction, orbit descent and final assembly.
Worker 1095 implemented the imported elementary orbit-limit theorem.
