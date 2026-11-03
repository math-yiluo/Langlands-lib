# Affine representation of actual line-bundle isomorphisms

`PicardGroupoid.relativeIsomPresheaf f L M` is the presheaf of actual
isomorphisms between two families of line bundles on the relative space.
Here `T` is an arbitrary scheme over `S`, and `L` and `M` are objects of
the published actual Picard groupoid on `T ×_S X`. The construction uses
the existing relative pseudofunctor's `presheafHom`, precomposes with
`T.iteratedSliceBackward.op`, and raises the value universe by
`uliftFunctor.{u + 1}`. Consequently its restriction maps retain the
published ordinary pullback and the pseudofunctor's coherence
isomorphisms. A point is an actual groupoid arrow, hence an isomorphism
of the pulled-back line bundles. It is not an isomorphism class.

`ProperLineBundleIsomRepresentabilityStatement.{u}` asks that for every
proper, flat, locally finitely presented morphism `f : X → S`, every
`T : Over S`, and every such pair `L, M`, there exist a scheme `I` over
`T.left` and a natural isomorphism
`schemeYoneda(T.left)(I) ≅ relativeIsomPresheaf(f,L,M)`.
The structure morphism of `I` must be affine and locally of finite
presentation. The natural isomorphism is defined on all of
`Over T.left`: tests include empty, nonreduced, nonnoetherian and
non-quasi-compact schemes. There is no hypothesis of projectivity,
noetherianness, smoothness, a section, or a condition on global functions.
The schemes and field consumers retain arbitrary universe `u`.

This is an internal statement for a focused rank-one route to the
Picard-stack atlas. Its formulation combines the already published
actual Picard pseudofunctor with the scheme-representation format of
`CoherentSheaves.ProperIsomRepresentabilityStatement`. The additional
ambient flatness hypothesis is permitted here because the atlas consumer
is over a field. The conclusion concerns line bundles, and makes no
assertion about arbitrary coherent source modules. No external
representability theorem is imported or proved by this statement.

A proof can use the actual fully faithful Picard-to-family inclusion,
compare its full-slice Isom presheaf with this direct construction, and
apply the published Isom equalizer to the four relevant Hom presheaves.
Those Hom representations and the natural comparison remain proof
obligations. This file supplies neither Isom representability nor a
smooth atlas; affine Isom representation is only one prerequisite for
the exact `FieldPicardStackAtlasStatement`.
