# Underlying topology in étale target descent of open immersions

This module proves that an analytic morphism whose base changes along a
jointly surjective étale target family are analytic open immersions has an
open embedding as its underlying point map. In particular its point-set
image is open. It does not assert that the morphism is an analytic open
immersion: constructing an analytic inverse onto that open domain still
requires descent of analytic morphisms.

It constructs the analytic domain on that open image and the canonical
factorization of the given morphism through it.

The field `K : Type u` is complete, ultrametric and normed; its valuation
need not be nontrivial. All analytic objects are in
`LocalizedCategory.{u, u, u}` because the imported point-lifting theorem
has precisely that scope. The target family has arbitrary indexing
universe: `ι : Type w`. The hypotheses supply `g i : V i ⟶ Y` jointly
surjective on points and actual categorical pullback squares of
`f : X ⟶ Y` with projections `p i : P i ⟶ X`, `q i : P i ⟶ V i`.
The final two theorems assume each `g i` étale and each `q i` an analytic
open immersion.

## Implemented proof

`preimage_image_eq_image_preimage_of_isPullback` proves, for any subset
`S` of the point space of `X`, the identity
`g⁻¹(f(S)) = q(p⁻¹(S))`. One direction uses the published
`exists_point_of_isPullback` to lift the compatible pair consisting of a
point of `S` and a point over its image. The reverse direction applies the
point-space functor to the square's commutativity.

`image_eq_iUnion_of_isPullbacks` uses the jointly surjective target family
and that identity to express `f(S)` as the union of the subsets
`g i (q i ((p i)⁻¹(S)))`. Consequently
`isOpenMap_of_etalePullbacks` proves that `f` is open whenever each `q i`
has an open point map: continuity makes `(p i)⁻¹(S)` open, openness of
`q i` preserves it, and the published `etaleOpenMap` does the same for
`g i`. The union is open.

`injective_of_pullbacks` needs neither étaleness nor openness. For two
points with the same image under `f`, choose a point over that common
image in one target chart. Lift each compatible pair to the same pullback
object. Injectivity of the point map of `q i` identifies the lifts, and
their first projections identify the original points.

`isOpenEmbedding_of_openImmersion_etalePullbacks` applies these two
results with the injective open point maps of the local analytic open
immersions. Continuity of `f` gives an open embedding.
`isOpen_range_of_openImmersion_etalePullbacks` extracts its open range.
`openImageDomainOfEtalePullbacks` constructs the open analytic domain on
that range using the published `openDomain`.
`openImageLiftOfEtalePullbacks` factors `f` through it by `domainLift`,
since each point `f(x)` lies in the range of `f`.
`openImageLiftOfEtalePullbacks_comp` is the factorization identity supplied
by `domainLift_comp`. No inverse to that analytic factorization is
constructed.

No uniqueness of compatible point lifts is asserted or used. The analytic
pullback point space is not identified with the ordinary fibre product
of topological spaces.

## Provenance and scope

This is an internal consequence of the published `LocalizedPullbackPoints`,
`EtaleOpenMap.Proof` and `AnalyticImmersion` modules. It introduces no
new geometric input and assumes no unproved sibling proposition. The
set identities, openness and injectivity arguments above are the
implemented route.

The result supplies the topological part of étale target descent needed
in the algebraic-space analytification immersion comparison. An open
embedding on point spaces does not supply its full analytic conclusion,
and this module claims no proof of that comparison.
