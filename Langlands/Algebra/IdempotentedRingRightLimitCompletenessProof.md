# Density and completeness of actual right-compatible families

Authors: Worker 6 and Worker 1155. The Lean proof reuses Worker 6's
focused shared draft (whole-book task `f5d1f399-a1f8-4ab5-a981-90b92abd4857`,
draft revision 2, content
`6a34b1a5d3b117281885dd751cf9b38c47f6bb6ee97185a982b54b01e2be9bd3`).
Worker 1155 checked the source correspondence and exact dependency boundary,
prepared this focused submission, and reran the development checks.
This is the proof of the published proposition
`Langlands.Algebra.IdempotentedRingRightLimitDensityCompletenessTheorem`,
prepared for exact-target proof task
`53ca8b48-65a8-400e-b1a9-260fa8fad191`.
The target and its imports are used by Lean name without changes.
The proof has no additional hypotheses. Development compilation and
shared draft status do not establish independent proof acceptance or
Library publication.

The target uses the actual compatible-family subgroup and its actual
coordinate uniformity. It combines closedness and completeness for
every original `NonUnitalRing A` with canonical density and dense
embedding under `IsIdempotented A`, at arbitrary original-ring
universe `uA`. It retains zero rings and noncommutative nonunital
operations without countability or nontriviality assumptions.

`idempotentedRingRightLimit_closedFamily` installs the discrete
uniformity on the original ring and its product uniformity on all
coordinate functions. It rewrites the actual carrier as the
intersection of the sets defined by every right-fixed equation
`x(e)*e = x(e)` and every coherence equation
`x(f)*e = x(e)` for `e ≤ f`. Coordinate evaluations are continuous.
Right multiplication by a fixed original element is continuous on a
discrete space. Both sides of each equation are therefore continuous
into discrete Hausdorff `A`, so each equality set is closed.
Arbitrary intersections and the intersection of the two families
prove closedness. This argument needs no local-unit condition.

`idempotentedRingRightLimit_complete` uses completeness of discrete
`A`, completeness of the arbitrary product, and completeness of the
closed compatible-family subset. The already constructed exact
`uniformSpace_eq_subtype` identifies its subspace uniformity with the
actual `IdempotentedRingRightLimit.uniformSpace A`. Rewriting along
that equality proves completeness for the actual carrier and
uniformity. No assumed completion or completeness certificate occurs.

`idempotentedRingRightLimit_canonicalDense` uses the exact
single-coordinate neighborhood basis supplied under
`IsIdempotented A`. Given a family `x` and a coordinate `e`, choose
the original element `x(e)`. Its canonical family's value at `e` is
`x(e)*e = x(e)` by the right-fixed family condition. It belongs to
the canonical range and the specified coordinate neighborhood.
The neighborhood-basis closure criterion gives density.

`idempotentedRingRightLimit_canonicalDenseEmbedding` combines this
density with the already proved exact uniform-inducing canonical
map and its algebraic injectivity from finite local units. The
topologies in this assertion are precisely those of the original
`idempotentedRingUniformSpace A` and the actual family uniformity.
The final theorem packages these four proofs into the exact closed
master target. Complete unapplied checks preserve `uA`.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.1.3, printed p.9/PDF15, gives the density argument and leaves
completeness to the reader. The coordinate-density proof implements
that argument at `f = e`. The closed-product proof supplies an
internal solution to the completeness exercise, with the stronger
arbitrary-nonunital-ring generality stated in the exact target.
Closedness and the Mathlib dense-embedding formulation are internal
supporting consequences, not numbered source theorems or a printed
completeness proof attributed to Renard.

This contribution contains only this new Lean/Markdown proof pair.
The target statement and its imported Library dependency closure are
unchanged. Development checks use environment
`3b864ddf-f0af-4c18-8903-c6f813a0ce0f`. The module compiles with zero
errors or warnings, and complete master-declaration inspection reports
level parameter `uA` and only `propext`, `Classical.choice` and
`Quot.sound`. Independent review and publication remain separate
requirements. Worker 1155 read the retained original PDF14–15 and
the relevant first page of the 2010 errata while preparing this submission.
The target does not request a uniform equivalence with
`UniformSpace.Completion`, a universal extension property, continuity
of limit multiplication, quotient comparisons or module-action
extensions; those remain separate units.
