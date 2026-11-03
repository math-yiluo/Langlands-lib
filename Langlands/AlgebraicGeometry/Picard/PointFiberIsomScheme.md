# Actual Picard point fibres from product-base Isom schemes

This internal construction turns a supplied scheme representation of
the direct product-base line-bundle Isom presheaf into a scheme
representation of the actual Picard point fibre. It preserves the
scheme universe `u`, actual line bundles, ordinary pullbacks and
their pseudofunctor coherence, and every test scheme in the full slice.

For a line bundle `L` over `U` and a line bundle `M` over `T`,
`PicardGroupoid.productIsomComparison` compares the generic product Hom
presheaf of `relativeHomLift f` with `relativeIsomPresheaf f` of the
two projection pullbacks on `U × T` in `Over S`. The lift's fibre
categories remain groupoids because the original categories are cores
and `ULiftHom` is a category equivalence. The Hom-presheaf comparison
`PseudofunctorHomLift.presheafHomIso` is precomposed with the full
iterated-slice functor and then reassociated. Thus the comparison
includes all coherent restriction maps.

Given a scheme `I` over the underlying product scheme and a natural
representation of that direct Isom presheaf by `I`,
`pointFiberIsomSchemeIso` composes three natural isomorphisms:
the product comparison just described, the generic
`Stacks.pointFiberSchemeIso`, and the concrete
`pointFiberPresheafHomLiftIso`. The resulting target is the published
actual `PicardGroupoid.pointFiberPresheaf f L M`, whose points retain
both a map to the atlas parameter scheme and an actual bundle
isomorphism. The representing scheme is `Stacks.pointFiberScheme I`;
its map to `T.left` is
`I.hom ≫ (prod.snd : U × T ⟶ T).left`.

The lemma `exists_pointFiberIsomScheme_of_properLineBundleIsom` assumes
the exact proposition `ProperLineBundleIsomRepresentabilityStatement`
and properness, flatness and local finite presentation of `f`. It
applies that proposition to the product base and the two actual
projection pullbacks. It retains the affine, locally finitely
presented map `I.hom` to the product and uses the preceding natural
comparison to represent the entire Picard point fibre. These two
geometric predicates concern `I.hom`. They assert no smoothness or
surjectivity of its composite map to `T.left`.

The provenance is internal, using the published generic scheme-slice
construction and concrete Picard universe comparison. Worker 149
specializes Worker 214's coherent-family point-fibre adapter; the
Hom-lift naturality argument is also extracted from Worker 214's
`CoherentSheaves.IsomPresheaf`. Unlike the coherent-family formula,
the direct Picard formula requires the explicit lift comparison and
functor associator. The existing coherent-family and Picard modules
are unchanged. This pair proves the conditional representation
adapter; the focused Isom theorem and the construction of a smooth
surjective presentation remain separate obligations.
