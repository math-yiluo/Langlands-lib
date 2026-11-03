# Actual family Hom representations from intrinsic module Hom

This is an internal composition of the natural comparison in
`IntrinsicModuleHomPresheaf` with the representation construction in
`FiniteLinearModelGluing`. It supplies no new geometric model-existence
or descent theorem.

Fix an arbitrary morphism `f : X ⟶ S`, an arbitrary `T : Over S`, and actual
coherent-family objects `M N : FamilyGroupoid f T`, all in universe `u`.
Let `p` be the actual projection from the relative space over `T` to
`T.left`. The intrinsic presheaf here is
`intrinsicModuleHomPresheaf p M.of.obj N.of.obj`. It consists of all
ordinary pulled-back module maps, with the explicit lift to `Type (u + 1)`.
The published `homPresheafIntrinsicIso` compares it naturally with the
actual family Hom presheaf on the entire slice over `T.left`.

`homPresheaf_hasLocalModels_of_intrinsic` transports local finite homogeneous
linear models from this intrinsic presheaf to the actual family Hom presheaf.
It uses invariance of `HasLocalModels` under natural isomorphism, with the
inverse of the published comparison.
`homPresheaf_isSheaf_of_intrinsic` transfers the fppf sheaf property through
that same comparison, by invariance of sheafness under natural isomorphism.
Both the models and sheafness are explicit premises of these transfer lemmas.

`exists_homRepresentation_of_intrinsic` assumes both properties of the
intrinsic presheaf. The proof obtains an actual `H : Over T.left` from
`HasLocalModels.exists_affine_representation`, together with a natural
isomorphism from its lifted functor of points to intrinsic Hom and both
`IsAffineHom H.hom` and `LocallyOfFinitePresentation H.hom`. Composing that
isomorphism with the inverse family-to-intrinsic comparison represents
`FamilyGroupoid.homPresheaf f M N`. The scheme and its structure map are
unchanged, so the two morphism properties remain properties of that same map.

`homRepresentationOfIntrinsic` chooses the scheme, natural representation
isomorphism, and both morphism properties from this proved existence theorem.
Its result is a dependent pair with a subtype of isomorphisms carrying the
two properties.

These results retain every test scheme and every slice arrow. They introduce
no properness, noetherianness, affineness, or rank restriction on `f` or the
tests. Their hypotheses still require the intrinsic local-model and fppf
sheaf theorems. In particular this conditional adapter does not establish
`ProperHomRepresentabilityStatement`; the actual geometric premises must
still be discharged in its stated scope.
