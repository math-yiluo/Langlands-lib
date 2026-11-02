# Bounded pushouts of actual relative Laurent annuli

This internal construction proves the bounded pushout property of the actual
relative Laurent annuli from `RelativeLaurentGaussSection` and
`RelativeLaurentTransport`. It derives the property directly from the scalar
weighted series evaluation and the imposed inverse equation. Its provenance is
this explicit universal-property argument, rather than a numbered result from
the literature.

## Parameters and quotients

Let `K : Type u` be an ultrametric normed field, let `t > 0`, and let `A` and `B`
be actual presented affinoid algebras over `K`. Write `A_t` and `B_t` for
`RelativeLaurentAnnulus.algebra K A t` and its analogue for `B`. These are the
enlarged scalar weighted Tate quotients retaining the old coefficient relations,
adjoining two variables with radii `(t,t⁻¹)`, and imposing their product equal
to one. The structural maps are `baseMap K A t` and `baseMap K B t`.

The target `E : Type v` is a normed commutative `K`-algebra; its universe is
independent of `u`. The evaluation constructions assume that `E` is complete
and ultrametric. They do not require a contractive coefficient map.

For a bounded map `α : A_t → E`,
`hasBoundedMonomials_map_newCoordinate` proves boundedness of the monomials in
the images of the two new coordinates, with their given reciprocal radii. The
proof maps the finite product through `α` and combines the positive bound
constant of `α` with the existing quotient-coordinate monomial estimate.
Neither completeness nor the ultrametric property of `E` is needed here.
`map_coordinate_mul`, under the same weaker assumptions on `E`, maps the
actual quotient identity to show that the two images have product one.

## Evaluation with a bounded coefficient map

Given a bounded map `β : B → E` and a tuple `b : Fin 2 → E` with bounded
monomials and `b 0 * b 1 = 1`, `liftFromBase` constructs a bounded map
`B_t → E`. The scalar evaluation uses
`RationalPresentation.solutionTuple`: its old coordinates are the images under
`β` of the presentation coordinates of `B`, and its new coordinates are `b`.
The published `solutionTuple_bounded` combines the coefficient map's bound with
the new-coordinate bound.

`solutionTuple_relations` checks the defining relations. For an old relation,
`evaluate_included` identifies its value with `β` applied to its zero image in
`B`. The remaining relation is exactly `b 0 * b 1 - 1`, which vanishes by the
given inverse equation. The existing `evaluateRelations` then descends scalar
evaluation through the actual closed generated relation ideal.

`liftFromBase_baseMap` and `liftFromBase_comp_baseMap` show that this map
restricts to `β`. Surjectivity of the presentation of `B` reduces the first
identity to `evaluate_included`. `liftFromBase_newCoordinate` gives the value
`b j` on each new coordinate, by the scalar coordinate evaluation formula.
These evaluation results do not require completeness of `K`.

## The pushout square

Now let `φ : A → B` be bounded and assume that `K` is complete, as required by
the existing construction `transport K t φ : A_t → B_t`. Its structural
identity makes the square with the two `baseMap` maps commute.

For bounded maps `α : A_t → E` and `β : B → E`, `pushoutLift` is
`liftFromBase` with new tuple given by the images of the source annulus
coordinates under `α`. The preceding monomial and inverse-equation lemmas
supply its hypotheses. The map itself does not depend on `φ` and is defined
before imposing compatibility. It always restricts to `β` on `B` and agrees
with `α` on the two new coordinates.

If `α.comp (baseMap K A t) = β.comp φ`, then
`pushoutLift_comp_transport` proves that its composition with `transport φ` is
`α`. The existing annulus `hom_ext` reduces this to equality on the
coefficient image and the two new coordinates. The coefficient case uses the
compatibility equality; the coordinate case uses
`transport_newCoordinate` and `pushoutLift_newCoordinate`.

`pushout_hom_ext` proves uniqueness from agreement on the two legs of the
square. Agreement on `B` follows directly from the structural leg; agreement
on new coordinates follows by evaluating agreement on the transported leg at
the source coordinates. This uniqueness lemma allows an arbitrary normed
commutative target, without completeness or ultrametric hypotheses.

Finally, `existsUnique_pushoutLift` combines these constructions: every
compatible pair of bounded maps from `A_t` and `B` into a complete ultrametric
normed `K`-algebra extends uniquely to a bounded map from `B_t`.

## Scope

The construction retains the full universe `u` and arbitrary positive real
radius, including trivially valued base fields. It assumes no radius
independence, strictness, reducedness, nonzero algebra, or contractivity.
The result concerns the actual enlarged weighted quotients and their bounded
maps. It supplies a supporting universal property; the host finite ambient
rational covering proposition remains open.
