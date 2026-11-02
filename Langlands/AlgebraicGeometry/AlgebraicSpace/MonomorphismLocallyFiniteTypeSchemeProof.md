# Schemehood for locally finite type monomorphisms into schemes

`Langlands.AlgebraicGeometry.AlgebraicSpace.monomorphismLocallyFiniteTypeScheme`
proves the exact published proposition
`MonomorphismLocallyFiniteTypeSchemeStatement.{u}`. For every base scheme
`S`, algebraic space `X` over `S`, and scheme `Y` over `S`, it assumes a
monomorphism `f : X.presheaf → h_Y` and an etale, surjective scheme atlas
`a : h_W → X.presheaf`. The atlas composite is an actual scheme map
`w : W → Y`, locally of finite type. The conclusion supplies an actual
scheme `V` over `S` and a natural isomorphism `h_V ≅ X.presheaf`.
The universe `u` is arbitrary.

The entry proof applies
`monomorphismLocallyFiniteTypeScheme_of_affine_etale_compact_images`
with the compact scheme and actual natural isomorphism returned by
`EtaleLocalImageDescent.affineEtaleImageModel` over every base scheme.
That construction selects witnesses from the proved theorem
`EtaleLocalImageDescent.of_affine_etale`, so it discharges the
compact-image assumption of the assembly theorem. There are no additional
assumptions on the original base, target, atlas, algebraic space, or their
morphisms.

The implemented argument is the monomorphism case of Stacks Lemma
67.27.10 (Tag 0463) and Proposition 67.50.2 (Tag 03XX), with the
finite-degree induction of Lemma 67.50.1 (Tag 03XW). The original 0463
and 03XX passages are registered as
`stacks-mono-lft-schemehood-2026-11-02`; 03XW is registered as
`stacks-03XW-2026-11-02`. The proof is organized through the following
concrete constructions.

`MonomorphismAtlasGeometry` identifies the atlas kernel pair with
`W ×_Y W`. Its etale projections make `w` unramified and locally
quasi-finite. `AffineAtlasNeighborhoods` restricts the source and
target near each atlas point to affine schemes. The scheme Zariski
main theorem in `EtaleLocalFiniteCharts` then provides an affine finite
chart after an etale base change, with a point over the original atlas
point. `EtaleFiniteChartQuotient` uses its finite etale kernel pair
and the finite locally free affine quotient theorem to represent its
local image in the base-changed sheaf by an affine open chart.

`EtaleLocalImageInduction` descends the image of that open chart.
An etale morphism between affine schemes has a finite bound on its
field-valued fibres. In degree at most one it is an open immersion.
For the induction step, `EtaleOffDiagonal` removes the diagonal from
the affine self-pullback and lowers the fibre bound. The induction
hypothesis represents the off-diagonal image. `OpenChartUnion` and
`CompactLocalImage` glue it to the original chart, and
`EtaleImageSaturation` identifies this compact represented union with
the full inverse image of the desired local image.

`EtaleLocalImageDescent.compactImageDescent` discharges the induction's
remaining effective-descent interface. `SaturatedLocalImageGeometry`
constructs the actual cartesian compact scheme above the local image.
Its monomorphic, locally finite type and locally quasi-finite map to
the affine base makes it quasi-affine by Zariski's main theorem.
`LocallyQuasiFiniteDescent.exists_iso_of_quasiAffine` constructs the
descended scheme using global functions and the common-kernel
comparison. The projection to the descended scheme is etale and
locally surjective, hence surjective on points. Compactness descends
along this continuous surjection. This proves the full compact-image
theorem used by the entry proof.

Finally, `AffineEtaleImageAssembly` converts these representations
into `HasRepresentedImage` for every finite affine chart. Replacing
the finite chart by its affine open image preserves the local image
because its map to that image is locally surjective.
`AffineAtlasChartReduction` gives open scheme charts with compatible
point lifts over every original atlas point.
`PointLiftedOpenCharts` proves their joint local surjectivity and
applies the published open-chart gluing theorem. All charts and their
structure morphisms remain over `S`, and their index type lies in
universe `u`. This yields the actual scheme and natural isomorphism
required by the unchanged target statement.
