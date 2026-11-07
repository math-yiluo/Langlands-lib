# Compact etale images inside representable open subfunctors

Author: Worker 133.

This internal module constructs actual open algebraic subspaces from etale
scheme charts. It also restricts a scheme chart to an affine open through a
specified point so that its sheafified image lies in a prescribed open.
The base scheme is arbitrary.

## Image construction

In namespace
`Langlands.AlgebraicGeometry.AlgebraicSpace.CompactEtaleImages`,
`imageSubfunctor a` is the fppf sheafification of the range subfunctor of
an actual scheme chart `a`. If `a` is representably etale,
`etaleImage Y a ha` packages this subfunctor as an actual open algebraic
subspace of `Y`, using `OpenSubspaceGeometry.openSubspace` and the published
`OpenSubfunctorImages.sheafify_range_open`.

`imageAtlas` is the canonical factorization of `a` through that image.
The published results `toRangeSheafify_isEtale` and
`toRangeSheafify_isSurjective` show that this is an etale geometrically
surjective atlas. Consequently `etaleImage_isQuasiCompact` proves absolute
quasi-compactness of the image whenever the source scheme is compact.
`etaleImage_isQuasiSeparated` uses open-subspace inheritance to retain
relative quasi-separatedness of the ambient space.

`imageSubfunctor_le_open` proves that any representable open subfunctor
containing the range of a chart also contains its sheafified range. The
proof uses detection of membership in an open on an fppf covering sieve.

## Restriction through a specified point

`exists_affine_restriction_inside_open` starts with any scheme chart
`a : (schemeYoneda S).obj U ⟶ Y.presheaf`, a representable open subfunctor
`A`, and an actual point `x : U.left`. Its hypothesis says that the
residue-field value of `a` at `x` belongs to `A`.

It produces an actual affine scheme `V : Over S`, an actual open immersion
`j : V ⟶ U`, and a point `d : V.left` with `j.left d = x`, such that the
whole sheafified image of `(schemeYoneda S).map j ≫ a` is contained in `A`.
There is no closed-point restriction and the input chart need not be etale.
If the input chart is etale, its open restriction is etale as well; the
preceding image construction then gives a quasi-compact open subspace
inside `A`.

The implemented proof represents the inverse image of `A` in `U`. The
published residue-field membership criterion shows that its open-immersion
projection contains `x` in its topological range. Choose a point over `x`
and an affine chart through that point. Composing the two open immersions
gives `j`. The represented pullback square proves that this restricted
chart factors through `A`, and `imageSubfunctor_le_open` gives the final
containment.

All constructions and lemmas are internal consequences of the named
Library APIs and scheme affine covers. This module supplies no
quasi-affine-source AF descent proof or final AF-source descent theorem.
