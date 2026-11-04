# Affine product representations of actual Picard point fibres

This internal consequence connects the published focused line-bundle Isom
theorem with the published `PointFiberIsomScheme` construction. It adds the
finite-presentation consequence needed when using these schemes for an atlas.
It introduces no new assertion from the literature.

`PicardGroupoid.HasAffinePointFiberSchemes f` quantifies every pair of parameter
schemes `U, T` over the base and every actual line-bundle family `L, M` over them.
It asks for a scheme `I` over the underlying product `(U × T).left`, affine and
locally of finite presentation over that product, such that
`Stacks.pointFiberScheme I` naturally represents the full actual
`pointFiberPresheaf f L M` over `T.left`. The structure map of this last scheme
is the composite of `I.hom` with the second product projection.

`hasAffinePointFiberSchemes` proves this proposition for a proper, flat,
locally finitely presented morphism `f`. It supplies the already published
`properLineBundleIsomRepresentability` to
`exists_pointFiberIsomScheme_of_properLineBundleIsom`. Thus the construction
uses the existing natural comparison, including the ordinary pullback
isomorphisms, their coherence and the explicit lift of section types.
It retains specified isomorphisms on every slice test, rather than passing
to isomorphism classes.

`exists_locallyOfFinitePresentation_pointFiberScheme` additionally assumes
that `U.hom` is locally of finite presentation. The two underlying projections
of the product in `Over S` form a pullback square. Stability under base change
therefore makes the second projection locally of finite presentation.
Composition with the locally finitely presented map `I.hom` gives local finite
presentation of `Stacks.pointFiberScheme I` over `T.left`. The conclusion
retains the same affine representation over the product.

The two field consequences retain the arbitrary universe `u` and every field,
including imperfect fields. Properness of the source is their only assumption
on that source. Mathlib's existing instances derive flatness for a morphism to
the spectrum of a field and local finite presentation from finite type over
this noetherian base. For the last consequence, local finite type of `U.hom`
likewise implies its local finite presentation. No finiteness or reducedness
condition is imposed on `T` or any scheme testing the represented presheaf.

These results construct scheme representations and prove their stated
finiteness properties. They do not establish smoothness or surjectivity over
`T`, choose a family whose maps have these properties, or prove the atlas
existence statement. In particular, affineness here concerns `I.hom` to the
product, and is not asserted for its composite to `T.left`.
