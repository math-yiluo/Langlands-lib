# Concrete scheme quotients on a tuple threshold

This module gives concrete quotient schemes for the cross-cover action and for
a compatible action on its pair scheme. It is derived infrastructure for the
symmetric-tuple filtration in Stacks Project, Lemma 68.8.6, Tag 07ST, and
Lemma 68.8.3, Tag 0BBN. The registered originals are
`stacks-noetherian-approximation-2026-11-01` and
`stacks-stratification-2026-11-02`. Those sources supply the tuple charts and
their image filtration. The quotient identifications here are internal
scheme-valued consequences of the previously established cross-cover geometry;
they are not additional approximation assumptions.

Work in arbitrary universe `u`. Assume the original relation `E` has separated
source, affine object and arrow schemes, and closed joint endpoint map. Fix
`p ≤ q < N+1`. Write `L` for its finite tail beginning at `p`, `H` for the tail
beginning at `q`, `P` for the cross-cover scheme, `c : P → H.U` for its source,
and `v : P → L.U` for its target. Let `W` be the `q`th threshold open in `L.U`.
The existing map `w : P → W` is étale and surjective, with `w;ι = v`.
Write `A` for the actual higher-tail action on `P`.

`tupleTailThresholdSchemeQuotient` packages `W` and `w` as a
`SchemeQuotient` of `A.relation`. Its kernel-pair square is the previously
proved threshold kernel-pair square; its étaleness and surjectivity are the
existing instances for `w`. No gluing or choice of a new quotient scheme is
needed.

Let `B = P ×_{H.U} P` with projections `a,b`. The existing pair arrow
`d : B → L.R` has target `a;v` and source `b;v`.
`tupleTailThresholdPairCover` lifts its reverse `d;L.inverse` to the
chart-relation arrows on `W → L.U`. The endpoint lemmas
`tupleTailThresholdPairCover_t` and `tupleTailThresholdPairCover_s` give,
respectively, `b;w` and `a;w`.
`tupleTailThresholdPairCover_map` says that forgetting the chart endpoints
gives `d;L.inverse`. This orientation makes the first pair projection the
source and the second the target.

`tupleTailThresholdPairCover_eq_arrow` shows that equality after this lifted
cover implies equality after `d`: forget the chart lifts, compose once more
with `L.inverse`, and use its involutivity.
`tupleTailThresholdPairCover_isPullback` proves the cartesian square whose
top map is the lifted cover, left map is `b`, right map is the target of the
chart relation, and bottom map is `w`. For any test scheme, forget and reverse
a chart arrow and lift it together with the prescribed second cross arrow
through the existing square for `d`. The involution law identifies the
forgotten result with the supplied chart arrow. The open immersion `W → L.U`
then identifies its other endpoint. Uniqueness follows from the established
extensionality of the original pair scheme.

`tupleTailThresholdPairCover_etale` and
`tupleTailThresholdPairCover_surjective` follow from this square by base
change of the corresponding properties of `w`.

For the remaining declarations, supply an action `A₂` of `H` on `B`, over
`a;c`, and explicit equations `ha,hb` saying that it preserves the two lower
targets `a;v` and `b;v`.
`tupleTailThresholdPairAction_cover` proves invariance of the lifted cover
by the two endpoint equations and cancellation of `W → L.U`.
`tupleTailThresholdPairAction_isPullback` proves that this action relation is
the kernel pair of the lifted cover: equality after the cover implies equality
after `d`, so the existing pair-action kernel-pair theorem supplies the lift;
the action relation's endpoint extensionality gives uniqueness.
`tupleTailThresholdPairSchemeQuotient` packages these results as a
`SchemeQuotient` of `A₂.relation`, whose quotient scheme is exactly the actual
chart-relation arrow scheme on `W`.

This helper retains the action and compatibility equations as explicit
parameters. It does not construct the diagonal action, a descended system of
relations, or a Noetherian first level.
