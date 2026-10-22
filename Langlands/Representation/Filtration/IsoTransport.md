# Transport of representation filtrations along natural isomorphisms

This internal construction transports actual subfunctors and finite filtrations
along a natural isomorphism of representation-valued functors. It also constructs
natural isomorphisms of their successive quotient functors and proves invariance
of the existing ordered-filtration and gluing predicates. Author: Worker 194.

Let `F` and `F'` be functors from a category `C` to `Rep R G`, where `R` is a
commutative ring and `G` is a monoid, and let `e : F ≅ F'`.
For an actual subfunctor `S` of `F`, `RepSubfunctor.isoTransport S e` has at `X`
the inverse image of `S.obj X` under the linear map `e.inv.app X`. Thus its
vectors are exactly the vectors whose inverse image belongs to the original
subspace, as recorded by `mem_isoTransport`. Because `e` is an isomorphism,
this is also the image of the original subspace under `e.hom.app X`.
Equivariance of the inverse component proves invariance under the monoid;
naturality of that component proves preservation under every map of `F'`.

`isoTransportHom` and `isoTransportInv` restrict the forward and inverse ambient
components to these actual subspaces. `isoTransportIso` assembles them into a
natural isomorphism from `S.toFunctor` to its transported subfunctor. The two
inverse laws are proved by subtype extensionality and the ambient inverse laws.
The naturality proof is the ambient naturality equation on underlying vectors.

`RepSubfunctor.quotientNatMap` is the quotient construction used for transporting
graded pieces. Given subfunctors `S,T` of `F`, subfunctors `S',T'` of `F'`, and a
natural map from `T.toFunctor` to `T'.toFunctor` preserving the lower subspaces,
it descends that map to the existing quotient functors. Objectwise it uses
`Submodule.mapQ`. Equivariance and naturality are proved on representatives using
the surjective quotient projections. `quotientNatMap_projection` records its
value on a representative. No containment of `S` in `T`, or of `S'` in `T'`, is
required: the existing quotients use the lower subspaces pulled back to the
upper ones, so in general they are `T/(S ∩ T)` and `T'/(S' ∩ T')`.

`isoTransportQuotientIso` descends both components of `isoTransportIso` through
that construction. Their preservation of the lower subspaces follows directly
from the inverse-image definition. The inverse laws are checked on quotient
representatives and follow from the restricted inverse laws. The result is an
isomorphism of functors, with naturality already supplied by `quotientNatMap`.

`RepFunctorFiltration.isoTransport` applies subfunctor transport to every step.
Inverse images preserve the original pointwise inclusions, so monotonicity is
unchanged. The zero endpoint follows from injectivity of the inverse ambient
component; the full endpoint follows from the inverse image of the full
submodule. The number and order of steps remain fixed, including repeated steps
and zero-length filtrations. `isoTransport_step_obj` records the chosen steps.
`isoTransportGradedIso` applies the quotient isomorphism to each consecutive pair
of steps, in the direction from the original graded functor to the transported
one.

For supplied natural isomorphisms from each `pieces i` to `pieces' i`,
`RepFunctorFiltration.HasGradedPieces.isoTransport` composes the inverse of that
graded transport isomorphism with the original graded identification and the
supplied piecewise isomorphism. `HasOrderedFiltration.iso` transports the
witnessing filtration, and `hasOrderedFiltration_iso_iff` applies the same
construction to the inverse ambient and piecewise isomorphisms for the reverse
direction. `IsGluedFrom.iso` retains the witnessing permutation and uses the
piecewise isomorphism at its permuted index. `isGluedFrom_iso_iff` gives the
corresponding two-way invariance. Taking identity isomorphisms on the ambient
functor or on the pieces specializes these results to either kind of transport
separately.

The ring, monoid, carrier, category-object, and category-morphism universes are
independent. Both ambient functors and all pieces use the same representation
carrier universe, as required by their common target category. No topological,
smoothness, field, finite-dimensionality, or exactness hypothesis is used.

Provenance is internal algebraic transport of the published constructions in
`Langlands.Representation.Filtration.Definitions`, the only project import.
The maps, quotient operations, inverse laws, and invariance proofs are explicitly
constructed from those definitions and pinned Mathlib. No additional literature
claim is introduced. This unit supplies assembly tools for a geometric-lemma
proof; it does not construct a support filtration, identify an orbit quotient,
prove exactness of localization, or prove the geometric lemma itself.
