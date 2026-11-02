# Assembly of schemehood from compact affine etale images

This internal adapter connects a compact local-image theorem to the
existing `AffineAtlasChartReduction`. The scheme universe `u` is arbitrary.
It uses actual schemes, actual fppf sheaves and the Library's lifted
scheme Yoneda functor.

`AffineEtaleCompactImageRepresentability S` is an explicit proposition,
not a proved theorem. For an etale morphism `e : B → T` between affine
schemes over `S`, it considers a cartesian square of actual fppf sheaves
`G → F` over `h_B → h_T`, where `F → h_T` is monomorphic. Given an open
chart `a : h_V → G` with affine `V` and a locally finite type scheme
map `w : V → B` satisfying `a ≫ p = h_w`, it asks for a compact scheme
representation of the fppf local image of `a ≫ π`. It assumes no
surjectivity of `e`.

`EtaleAffineImageChart.hasRepresentedImage_of_affine_etale_compact_images`
assumes this proposition and an affine target for the given
`EtaleAffineImageChart`. The stored `imageAffine` supplies an affine
scheme `V` representing the local image of its finite chart, together
with an open map `b : h_V → G`. `RepresentedLocalImageGeometry` constructs
the locally finite type scheme map `q : V → B` and an etale surjective
map from the original finite chart to `V`. The assumed compact-image
proposition applies to `b` and `q`. Local surjectivity of that etale
scheme map shows that replacing the original chart by `b` leaves its
local image in `F` unchanged. Thus this compact representation gives
`C.HasRepresentedImage`.

The private local-image lemma proves that precomposing a map into an
fppf sheaf by a locally surjective map leaves its local image unchanged.
One inclusion follows from containment of ranges. For the other,
local surjectivity puts every section in the larger range locally in
the smaller range; monotonicity and idempotence of local closure finish.

`monomorphismLocallyFiniteTypeScheme_of_affine_etale_compact_images`
assumes the proposition over every base `S` and proves the exact published
`MonomorphismLocallyFiniteTypeSchemeStatement`. It uses the preceding
adapter in every affine atlas neighborhood, then applies
`exists_representation_of_affine_etale_images` for point coverage and
open-chart gluing.

The compact-image proposition remains an explicit assumption. This module
constructs neither effective descent nor its induction, and therefore
does not prove the unconditional schemehood statement. Its provenance
is the internal assembly specified jointly by Workers 122 and 1150,
using `AffineAtlasChartReduction`, `RepresentedLocalImageGeometry`,
`CompactLocalImage`, and local surjectivity of represented fppf covers.
