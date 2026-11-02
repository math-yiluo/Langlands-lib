# Inclusion of actual line bundles into flat finitely presented families

For a flat scheme morphism `p : X ⟶ Y`, `LineBundle.toFamily p` includes
actual line bundles on `X` in `CoherentSheaves.Family p`. The actual sheaf
does not change. Local rank one gives local finite presentation through
the constructed finite local presentations, and relative flatness through
the constructed actual stalk bases and flatness of `p`. The functor is
the standard inclusion between two full subcategories of `X.Modules`.
It therefore retains all actual module morphisms and is fully faithful.
`LineBundle.toFamilyForgetIso` identifies its composite with the family
forgetful functor with the original line-bundle forgetful functor.

`PicardGroupoid.toFamily p` applies the core construction. Its objects
are the same actual sheaves, and its arrows are the same actual module
isomorphisms regarded in the family category. The explicit
`toFamilyFullyFaithful` lifts a family-core arrow by forgetting to its
actual module isomorphism and including that isomorphism in the full
line-bundle subcategory. Extensionality of core arrows and full-subcategory
maps proves both inverse identities.

For a flat ambient morphism `f : X ⟶ S`, `relativeToFamily f T` specializes
this construction to the actual projection `T.left ×_S X ⟶ T.left`.
This projection is flat by base change. Its source is exactly the
published actual relative Picard groupoid on `T.left ×_S X`, and its target
is `CoherentSheaves.FamilyGroupoid f T` on that same fibre product.
`relativeToFamilyFullyFaithful` proves full faithfulness for every
`T : Over S`. The final equalities expose the unchanged module on objects
and the unchanged module-isomorphism homomorphism on arrows.

This is an internal construction from the published actual line-bundle,
family, and relative-space interfaces and the two elementary line-bundle
finiteness and flatness results. It is uniform in the universe and the full
test-scheme slice, including empty and non-quasi-compact tests. It assumes
only flatness of the ambient morphism. Pseudofunctor naturality and the
geometric atlas construction are separate obligations.
