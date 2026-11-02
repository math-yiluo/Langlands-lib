# Restricting an actual coherent-family atlas to line bundles

This internal construction applies the rank-one open and the full-slice atlas
restriction to the actual coherent-family and Picard pseudofunctors. The scheme
universe `u` is arbitrary.

Let `f : X → S` be flat, universally closed and locally of finite presentation.
The explicit input `α` is a strong transformation from the hom-lifted actual
Picard pseudofunctor to the hom-lifted actual coherent-family pseudofunctor.
Its components must be fully faithful. The explicit equality `hobj` identifies
its action on every actual line bundle with the published inclusion
`PicardGroupoid.relativeToFamily`, retaining the underlying module.

For an actual coherent family `M` over `U`, `coherentRankOneAtlasImageIso`
uses `hobj` and `familyRankOneLineBundleIso` to identify the image of the actual
line bundle on `familyRankOneBase f M` with the ordinary pullback of `M` along
the open inclusion. The second isomorphism is the lift of an actual family
isomorphism whose underlying module isomorphism is the identity.

For each test line bundle, `coherentRankOneAtlas_points_factor` first uses
`hobj` to recover the rank-one property of its image module. The actual point
factorization then supplies a base map into the rank-one open with the required
composite. This works for every object of the full slice over the test scheme,
with the actual point isomorphism retained.

`PicardGroupoid.hasLocallyFiniteTypeSmoothSchemeAtlas_of_coherentAtlas` takes
an actual locally finite type smooth coherent-family atlas. Its scheme `U`
is replaced by the actual rank-one open, which remains locally of finite type
over `S`. The constructed line bundle, image isomorphism, and all-point
factorization supply the generic atlas restriction theorem. That theorem
transports the natural point-fibre representations using the same representing
schemes and smooth surjective maps. Finally the published hom-lift comparison
gives the original, concrete Picard atlas predicate.

The provenance is internal composition of the cited Library constructions.
The transformation, its object equality, full faithfulness and the actual
coherent-stack atlas remain explicit inputs. This pair supplies no
unconditional coherent-stack or Picard-stack atlas existence theorem.
