# Closed finite orbits of affine étale scheme relations

Authors: Worker 101 and Worker 239.

This internal construction connects the finite-orbit topology argument to
the actual underlying points of the published `EtaleEquivalenceRelation`.
Worker 239 supplied the host finite-orbit strategy. Worker 101 supplied
the finite-closure and topological discreteness refinements and their
implementation. No claim about comodule support or nonzero invariants is
made here.

`PointRel E x y` means that a point of `E.R` has source `x` and target `y`.
The relation is reflexive and symmetric by evaluating the published
scheme-valued relation axioms on identity morphisms. For transitivity,
Mathlib's surjectivity from scheme pullback points to the corresponding
pairs of underlying points supplies a point of `R ×_U R` over two
composable points. Evaluating the scheme-valued transitivity axiom there
gives the composite point. Thus `pointSetoid E` is the actual point
equivalence relation.

`PointInvariant E T` means that membership in `T` is preserved by this
relation. Its source and target preimages agree. Both projections are
continuous and open, since étale maps are flat and locally finitely
presented, so closure preserves invariance. Étale source maps are locally
quasi-finite; when both schemes are affine, the source is quasi-compact.
Its point fibers are therefore finite. The class of `x` is the target
image of its source fiber, which proves `pointRel_finite`.

For a Noetherian object scheme, `minimalClosedPointInvariant` chooses a
minimal nonempty closed invariant subset inside a supplied one. Its
specification records both containment and minimality. For affine object
and relation schemes, `eq_pointRel_of_minimal` identifies any such
minimal subset with the class of each of its points. It applies the
previous finite-closure topology construction, using exactly the actual
point relation, finite classes, and invariant closure.

The discreteness argument needs no restricted reduced scheme. A finite
nonempty T₀ space has an open singleton `{x}`. If a continuous map `s`
has discrete fibers, its fiber over `x` is both open and discrete. An
open map `t` sends that open discrete fiber to a discrete subset. If
every point is related to `x`, that image is the whole space. Hence the
space is discrete. The auxiliary result
`isDiscrete_of_finite_class` applies this argument after restricting
the maps topologically to an invariant finite subset. The equal source
and target preimages ensure that both restricted maps have the same
domain. Openness and source-fiber discreteness persist under these
restrictions.

Consequently `finite_discrete_closedPoints_of_minimal` proves that a
minimal nonempty closed invariant subset for the actual affine étale
relation is finite and discrete. Since it is also closed in the object
scheme, each of its points is closed in the object scheme. The theorem
requires a supplied minimal subset; the Noetherian choice construction
supplies one when a nonempty closed invariant subset has been given.

Support invariance for an actual coaction, restriction by its radical
ideal, quotient coactions and module descent remain separate obligations.
This module neither proves the nonzero-invariant proposition nor assumes
an affine quotient.
