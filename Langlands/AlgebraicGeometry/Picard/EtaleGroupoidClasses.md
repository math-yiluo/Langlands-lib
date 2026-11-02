# Etale classes of the actual relative Picard groupoid

This internal comparison applies etale sheafification to the published natural
isomorphism `PicardGroupoid.relativeClassPresheafIso`. That isomorphism identifies
the isomorphism classes of actual line bundles in the relative pullback
pseudofunctor with the ordinary relative Picard class presheaf. The present
construction uses the functoriality and unit naturality of Mathlib
sheafification. It assumes no external representability theorem.

For any morphism `f : X → S`, `relativeEtaleClassSheaf f` is the etale
sheafification of `relativeClassPresheaf f` on the entire category `Over S`.
`relativeEtaleClassSheafIso f` is the natural isomorphism to the already defined
ordinary `RelativePicard.etaleClassSheaf f`, obtained by applying the
sheafification functor to `relativeClassPresheafIso f`.

`relativeToEtaleClassSheaf` is the ordinary sheafification unit.
`relativeToEtaleClassSheaf_comparison` proves its compatibility with the two
class presheaves and their units, using `toSheafify_naturality`. The component
lemma applies this equality to the isomorphism class of an actual bundle on an
arbitrary relative test scheme.

For an actual scheme `U` over `S` and line bundle `L` on `U ×ₛ X`,
`etaleFamilyMap f L` is the natural transformation from the lifted Yoneda
presheaf of `U` to `relativeEtaleClassSheaf f`, determined by the etale class of
`L`. The implemented construction is the inverse of `uliftYonedaEquiv`.
`etaleFamilyMap_comparison` proves that composing this whole transformation
with `relativeEtaleClassSheafIso f` gives precisely the lifted Yoneda
transformation determined by the ordinary etale Picard class of `L`. The proof
uses compatibility of that Yoneda equivalence with composition and the
component comparison.

Every relative test scheme and every morphism is retained, including
nonreduced and non-quasi-compact tests. Functorial sheafification compares
the entire sheaves, so the isomorphism also applies to sections without a
global bundle representative. No field, properness, flatness, section,
global-functions or finiteness hypothesis is imposed. This module supplies
no fppf descent, stack quotient, or representability assertion.
