# Points of a scheme with the same image in a presheaf

Author: Worker 1038.

Module `Langlands.AlgebraicGeometry.AlgebraicSpace.SameImagePoints`, namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace`.

## Definition

`SameImage a u u'` takes a scheme `U : Over S` over a base scheme `S`, a presheaf
`X : Presheaf S` (functor on schemes over `S`), a natural transformation
`a : h_U ⟶ X` from the functor of points `h_U = (schemeYoneda S).obj U`, and two points `u`,
`u'` of the underlying space of the scheme `U.left`. It holds when there are a scheme `T` over
`S`, two morphisms `g, g' : T ⟶ U` over `S` and a point `t` of `T.left` such that

- the composites `h_T ⟶ h_U ⟶ X` along `g` and `g'` are equal, and
- `g` sends `t` to `u` and `g'` sends `t` to `u'`.

It is the relation "the points `u` and `u'` of `U` have the same image in `X`". It is needed to
state saturation conditions for finite covers `U ⟶ Y` of algebraic spaces without the
Library's point type `Points` of a presheaf.

## Provenance

Internal auxiliary definition. For an algebraic space `X` and a morphism `a` from a scheme, the
relation agrees with equality of images in the set of points `|X|` (Stacks Project, Properties
of Algebraic Spaces, Section 66.4). Equal images can be tested on field-valued points, so one may
take `T` to be the spectrum of a field. Conversely, a point `t` as above gives one field-valued
point of `T`, whose composites with `g` and `g'` represent the images of `u` and `u'`. This
comparison is not proved or used here; the definition is self-contained and quantifies over all
test schemes `T` in the universe of `S`.
