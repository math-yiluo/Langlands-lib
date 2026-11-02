# Actual points factor through the coherent family's rank-one open

This is an internal application of `CoherentFamilyRankOneOpen`, ordinary
module pullback, and the actual coherent-family point-fibre construction.
It introduces no new literature assertion.

Let `f : X → S` be universally closed and locally of finite presentation,
let `M` be an actual flat finitely presented family over `U`, and let `N`
be such a family over `T` whose underlying module is locally free of rank
one. For every object `Z → T` of the full slice, an actual point consists
of a map `a : Z → U` over `S` and an actual isomorphism `a*M ≅ p*N`.

`familyRankOnePoint_isLocallyFreeRankOne` pulls back the rank-one property
of `N` along the actual relative-space map for `p`. The underlying actual
module isomorphism of the point then transports that property to `a*M`.

`familyRankOnePointLift` applies the rank-one open's universal property to
this module. It gives an actual map from `Z` into `familyRankOneBase f M`.
Its composite with the actual inclusion is precisely `a`, as proved by
`familyRankOnePointLift_fac`. `familyRankOnePointLift_uniq` gives uniqueness
among all actual maps over `S` with that composite.

`familyRankOneHomLiftPointLift` and its factorization lemma apply the same
construction after forgetting the explicit hom-universe lift through the
published point equivalence. Forgetting the lift leaves the actual base
map unchanged. All tests remain arbitrary, and the scheme universe `u`
is arbitrary.

The module also records monicity of `familyRankOneInclusion` and local
finite type of the open scheme over `S` when `U` is locally of finite
type over `S`. These use the actual open immersion and its composition
with the structure morphism.

This is an actual point-factorization result, not an atlas existence proof.
It assumes the test family is rank one and constructs no coherent atlas or
strong Picard inclusion. The original geometric hypotheses on `f` and the
family conditions on `M` remain necessary inputs to the rank-one open's
universal property.
