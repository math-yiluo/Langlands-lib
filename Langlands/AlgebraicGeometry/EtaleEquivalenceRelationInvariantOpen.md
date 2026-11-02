# Invariant open subschemes of an étale equivalence relation

Author: Worker 706.

This internal scheme-level interface is used for the invariant open pieces
in the proof of Stacks Lemma 70.5.11, Tag 07SR, and Proposition 70.8.1,
Tag 07SU. The registered sources are
`stacks-stratification-2026-11-02` and
`stacks-noetherian-approximation-2026-11-01`. The declarations are derived
consequences of the scheme-valued relation axioms and the universal
property of an open immersion. They do not assert existence of a quotient
or a Noetherian first level. Everything retains arbitrary universe `u`.

`IsInvariantOpen E U` is the equality `E.s ⁻¹ᵁ U = E.t ⁻¹ᵁ U`.
`isInvariantOpen_top` and `isInvariantOpen_inf` prove that the full open
and the intersection of two invariant opens are invariant, using inverse
images of the corresponding lattice operations.

`isCartesianHom_chart_of_isInvariantOpen` says that the previously
constructed chart relation `E.chart U.ι` maps cartesianly to `E`, with
object map `U.ι` and arrow map `Chart.map E U.ι`. To prove the source
square is a pullback, start with an original arrow and a lift of its
source to the open. Invariance makes its target land in the open, so the
open immersion lifts that target uniquely. The universal property of
chart arrows supplies the required arrow with both lifted endpoints.
Uniqueness follows from the two chart endpoints and the monomorphism
`U.ι`.

In the namespace `IsCartesianHom`, `isInvariantOpen_preimage` pulls an
invariant open back along a cartesian relation morphism. Its proof uses
only compatibility with the two endpoints and functoriality of inverse
image.

`invariantOpenMap U` is the induced arrow map from the chart on
`f ⁻¹ᵁ U` to the chart on `U`. It is defined for every open `U`, without
an invariance hypothesis, by the existing chart comparison construction.
`isCartesianHom_invariantOpenMap` proves that this arrow map and the
actual object restriction `f ∣_ U` form a cartesian relation morphism.
The proof applies the chart-comparison theorem to the canonical
pullback square defining restriction of a scheme morphism. When `U`
is invariant, the preceding lemmas also identify the two chart relations
as invariant restrictions of the original relations.
