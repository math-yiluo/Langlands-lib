# Restriction of actual Čech descent data

This internal construction restricts the actual group-scheme data of
`Descent.Data`. It derives its constructors and laws from the published actual
transitions and comparison coherence of `Descent.Reindex`. All schemes lie in
one arbitrary universe. The square need only commute; no covering, flatness,
affineness, reducedness or quasi-compactness assumption is imposed.

Let `p : S → B`, let `G` be an actual group scheme over `S`, and let
`D : Datum p G`. Given `t : V → C`, `q : V → S` and `b : C → B` with
`q ≫ p = t ≫ b`, `Datum.reindex t q b w` constructs a datum on `t` for the
actual pullback of `G` along `q`.

Its `reindexOverlap` takes the original transition along the two maps
`fst t ≫ q` and `snd t ≫ q`, whose composites with `p` agree by the square
and the double-overlap equation. It converts that actual isomorphism to an
isomorphism between the iterated pullbacks using `reindexIso`.
`pullHom_reindexOverlap` identifies every further pullback of this overlap
with the correspondingly reindexed original transition. The implementation
uses `pullHom_reindexHom` and `Datum.pullHom_transition`.

The cocycle of the constructed datum follows by applying that restriction
formula on each of the three overlap projections, cancelling the middle
comparison using `reindexHom_comp`, and using `Datum.transition_comp`.
In particular, no new cocycle is required as an input.
`transition_reindex` gives the same formula for the new datum's transitions
on every pair of maps to `V` having equal composite with `t`.

`Datum.refine q` specializes the square to the composite cover `q ≫ p`
over `B`. `Datum.baseChange b` specializes it to the scheme pullback of `p`
along `b`, with the two actual pullback projections.

`reindexHom_map` identifies reindexing of the direct pullback of a
homomorphism with its iterated pullback, using naturality of the canonical
comparison. `Compatible.transition` pulls the original compatibility
equation back along the induced double-overlap map and distributes
`pullHom` over its two composites. It proves that every original transition
commutes with a compatible homomorphism.
`Compatible.reindex` applies `reindexHom` to that equation and uses
`reindexHom_map` to show that the pullback of the homomorphism is compatible
with the two restricted data.

These constructions restrict supplied actual data and compatible
homomorphisms. They do not construct a descent solution or establish
effective object descent, a pinning, or the quasi-split inner-form existence
statement.
