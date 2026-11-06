# Realization of invariant subgroups of finite étale commutative group schemes

Authors: Worker 1609 and Worker 1730.

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.invariantSubgroupRealization`
has exactly the published type
`Langlands.AlgebraicGeometry.FiniteEtale.InvariantSubgroupRealizationStatement.{u}`.
It retains the arbitrary universe, connected locally noetherian base,
algebraically closed geometric-point field, explicit fibre-finiteness premise,
and the actual group scheme and monodromy action. The realizing group scheme,
its finite étale structure, closed immersion and exact point image are all
constructed in the proof.

## Implemented construction

First, `liftPointMap` uses fullness of the continuous-action functor to lift an
equivariant function between actual geometric fibres to a morphism of covers.
Its application lemma follows from the functor's `map_preimage` identity.

The helper `realizePointSubset` forms the subtype of points whose additive
versions belong to the given subgroup `M`. Monodromy invariance makes it a
`SubMulAction`. Its continuity is inherited from the continuous evaluation
action on the ambient fibre with the subtype topology; discreteness identifies
that topology with the finite-set discrete topology. The published
`geometricContinuousActionEquivalence` realizes this finite continuous action by
an actual cover `Y`. The equivalence's object-preimage isomorphism gives an
equivariant bijection from `Fiber s Y` onto the subtype. Lifting the subtype
inclusion produces an actual slice morphism `i : Y.obj ⟶ G.X`, injective on the
chosen fibre, whose point image is exactly `M`.

The helper `pointMap_ext` uses faithfulness of the same functor to detect
equality of morphisms by their effect on this fibre. In `factorPointSubset`, a
map of covers whose point image is contained in the image of `i` has a unique
pointwise lift, since `i` is fibrewise injective. Naturality of monodromy makes
this lift equivariant. Fullness lifts it to a morphism, and faithfulness proves
the required factorization identity.

The final theorem applies this factorization to the identity, multiplication
and inverse of `G`. The needed image-containment assertions follow respectively
from `M.zero_mem`, `M.add_mem` and `M.neg_mem`. For multiplication the cartesian
product projections identify the pointwise map with the actual product of the
two included points.

The published `cover_mono_of_fiber_injective` shows that the underlying scheme
map of `i` is monic; it is consequently monic in the slice as well. The private
categorical construction `restrictedGroupObj` equips `Y.obj` with the lifted
unit, multiplication and inverse. It proves the group-object axioms by
postcomposing with this monomorphism and reducing to the ambient group laws.
The auxiliary `transfer_mul` computes these composites using cartesian product
projections. The same cancellation argument and ambient commutativity prove
commutativity on `Y.obj`. The factorization identities for the unit and
multiplication make `i` an actual group-object homomorphism, then a morphism of
`Langlands.CommGroupScheme S` in its existing additive notation.

The cover supplies finiteness and étaleness of the realizing structural map.
The underlying inclusion is finite because its composite with the structural
map of `G` is finite. Mathlib's
`AlgebraicGeometry.IsClosedImmersion.iff_isFinite_and_mono` therefore proves it
is a closed immersion. The point-image equivalence already proved for `i`
is definitionally the exact additive point-image conclusion for this
commutative-group-scheme morphism.

## Provenance and scope

This is an internal derived proof of the published target designed for the
commensurable invariant Tate lattice construction. It imports the statement,
`GeometricContinuousActionEquivalenceProof` and
`GeometricFiberConservativeProof` by Lean module name, and uses the actual
`CommGroupScheme` and finite-monodromy interfaces imported by the statement.
The categorical restriction helpers are proved here. There are no new
realization or transport hypotheses, axioms, characteristic assumptions or
quotient inputs. The proof does not alter the target or any imported pair.
