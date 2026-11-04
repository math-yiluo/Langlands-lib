# Proper maps on actual full-adele fixed-model points

This unit isolates the full-adelic properness step after a proper arithmetic
model has been chosen in Brian Conrad, *Weil and Grothendieck approaches to
adelic points* (December 31, 2011), printed p.11, Proposition 4.4, first two
proof paragraphs. The registered source is
`conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.

`CurvePlaceFixedModelProperMapStatement` quantifies over every function field
`F` over a finite field `k`, with the displayed compatible rational-function
action, every finite set `S` of actual curve places, and every proper model
morphism `f : X ⟶ Y` over the actual outside-`S` integer ring. The target is
locally of finite type, quasi-compact and separated over that integer base.
Postcomposition by `f` on actual points with coefficients in the full curve
adele ring is `IsProperMap` for the existing
`curvePlaceFixedModelAdelePointTopology` on each side.

`NumberFieldFixedModelProperMapStatement` is the corresponding assertion for
every number field. Here `S` indexes finite places; the full coefficient ring
includes every infinite completion. The topology on each side is
`numberFieldFixedModelAdelePointTopology`. The main statement is the conjunction
of these two universal assertions in arbitrary common universe `u`.

These are actual relative scheme points: morphisms from the spectrum of the
full adele algebra, with its original integer-base action, to the indicated
model. The topologies are final from all actual arithmetic levels containing
`S`, with the level topology transported through the actual model-base-change
point homeomorphism. `IsProperMap` is Mathlib's topological properness and
includes continuity. Neither model is assumed affine. Properness of `f` and
the displayed target hypotheses imply the same finite-type and separated
properties for `X`; no additional source hypothesis is needed. Finite type
here is expressed as local finite type and quasi-compactness.

The statement is derived from the indicated proof step: it retains the fixed
proper models rather than asserting their existence for an arbitrary proper
generic-fibre map. Its route uses the open cover of full target points by
arithmetic-stage images. The full-level valuative preimage equality identifies
the inverse image of each target stage with the source stage. Properness of
the corresponding map at that level then implies properness of the full map.
The extension to empty `S` follows by the same level argument. Finite curve
constants are used for compactness of the completed integer-ring factors.
The rational-function extension is not required to be separable.

The printed proof also writes an identification of target integral and field
points outside `S`; it is false for general targets, as the inverse of a
uniformizer on the affine line shows. This statement uses the correct
preimage equality for a proper morphism and compactness of integral source
factors in the level properness argument, and requires no such identification.

This unit states no proof. Proper-model spreading for arbitrary generic-fibre
morphisms, the comparison with the intrinsic adelic topology, compactness and
eventual stabilization, and the remaining assertions of the paper are separate
obligations of the parent program.
