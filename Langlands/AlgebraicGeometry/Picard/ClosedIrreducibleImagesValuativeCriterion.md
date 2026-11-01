# Closed irreducible images and valuative existence

`Langlands.AlgebraicGeometry.UniversallyClosedIrreducibleImages p`
requires `ClosedIrreducibleImages` after every scheme base change of the
displayed scheme morphism `p`. Base changes are those in Mathlib's
`MorphismProperty.universally`, in the same arbitrary universe `u`.
There is no quasi-compactness requirement.

This module is an internal adapter between the published
`ClosedIrreducibleImages` predicate and Mathlib's specialization and
valuative APIs. It makes no new assertion from external literature.

`closedIrreducibleImages_iff_specializingMap` proves that a scheme
morphism has closed images of closed irreducible subsets if and only if
it is a `SpecializingMap`: every specialization of the image of a point
lifts to a specialization of that point. In one direction, apply the
closed-image hypothesis to the closure of each singleton and use
Mathlib's `specializingMap_iff_isClosed_image_closure_singleton`.
For the converse, a closed irreducible subset of a scheme has a generic
point because schemes are sober. Replace that subset by the closure of
its generic point and apply the same Mathlib characterization. Neither
direction assumes quasi-compactness, finiteness, separation or
noetherianity.

`valuativeCriterionExistence_iff_universallyClosedIrreducibleImages`
applies this equivalence after every base change and uses Mathlib's
`ValuativeCriterion.Existence.eq`, which identifies full valuative
existence with universally lifting specializations. Thus the new
predicate is equivalent to `ValuativeCriterion.Existence p`. Here the
valuative squares use every valuation domain and every specified
fraction field, exactly as in Mathlib's `ValuativeCommSq`.

`closedIrreducibleImages_of_valuativeCriterionExistence` obtains the
published closed-image hypothesis on the displayed base directly from
Mathlib's `ValuativeCriterion.Existence.specializingMap` and the first
equivalence.

These statements do not restrict tests to discrete valuation rings or
to locally noetherian bases. They do not prove such a restriction is
sufficient. The universal predicate here quantifies over all scheme
base changes; it is not a definition of essential properness over a
locally noetherian base. It is also not Mathlib's `UniversallyClosed`,
which additionally requires quasi-compactness. No line-bundle,
generic-section-extension or host two-axis-extension conclusion is
asserted in this module.
