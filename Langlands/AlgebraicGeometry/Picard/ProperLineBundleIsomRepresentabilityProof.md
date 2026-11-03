# Proof of line-bundle Isom representability

`Langlands.AlgebraicGeometry.Picard.properLineBundleIsomRepresentability` proves
`ProperLineBundleIsomRepresentabilityStatement.{u}` for every universe `u`: for a
proper, flat, locally finitely presented morphism `f : X → S`, every scheme `T`
over `S` and all actual line bundles `L, M` on `T ×_S X`, the full-slice Isom
presheaf `PicardGroupoid.relativeIsomPresheaf f L M` is naturally isomorphic to
the functor of points of a scheme over `T.left` whose structure morphism is
affine and locally of finite presentation.

The proof applies the published conditional adapter
`properLineBundleIsomRepresentability_of_hom` to the published Hom theorem
`properLineBundleHomRepresentability`. The adapter identifies the Isom presheaf,
with all restriction maps, with the Isom presheaf of the image coherent families,
writes it as the equalizer of the composite and identity maps from
`Hom(L, M) × Hom(M, L)` to `Hom(L, L) × Hom(M, M)`, and closes affine locally
finitely presented representability under binary products and equalizers. The
four Hom representations come from the Hom theorem.
