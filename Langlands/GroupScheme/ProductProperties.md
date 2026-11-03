# Structure-morphism properties of finite products of group schemes

Worker 1424.

This module proves a general closure property of the finite products of group
schemes from `Products.lean`. Fix a morphism property `P` of schemes that is
stable under composition and base change, contains identities and respects
isomorphisms. If every factor of a finite product of group schemes has its
structure morphism in `P`, so does the product. This is a routine internal
lemma. It is used, for example, with `P = IsAffineHom` to show that a finite
product of affine group schemes is affine over the base.

## Binary products

`prop_tensor_hom P X Y hX hY`: for objects `X` and `Y` of `Over S` whose
structure morphisms lie in `P`, the structure morphism of the cartesian
monoidal product `X ⊗ Y` lies in `P`. Only stability under composition and
base change is used. The structure morphism of `X ⊗ Y` is, by definition,
`pullback.fst X.hom Y.hom ≫ X.hom`. The first projection is the base change of
`Y.hom` along `X.hom`, so it is in `P`, and composing with `X.hom` stays in `P`.

## Finite products

The private instance `overObj_closedUnderBinary` says that the full
subcategory `MorphismProperty.overObj P` of `Over S` (objects whose structure
morphism lies in `P`) is closed under binary products. Any binary limit cone
over a pair diagram is turned into a `BinaryFan` of the two diagram objects.
Its cone point is then isomorphic to `Y ⊗ Z` via
`tensorProductIsBinaryProduct`, and `prop_tensor_hom` together with invariance
under isomorphism (`prop_of_iso`) gives the claim.

`prop_pi_hom P G hG`: for a finite index type `I : Type u` and a family
`G : I → GroupScheme S` with `P (G i).X.hom` for every `i`, the structure
morphism of `(pi G).X` lies in `P`. Mathlib's
`ObjectProperty.IsClosedUnderFiniteProducts.mk'` upgrades closure under binary
products, plus the terminal object `𝟙 S` (which is in `P` because `P` contains
identities), to closure under all finite products. The underlying object of
`pi G` is a limit fan of the underlying objects `(G i).X` by the published
`piIsLimit`, so `prop_of_isLimit_fan` concludes.
