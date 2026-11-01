# Typed comparison of actual Jacquet support quotients

This internal construction compares the coordinate quotients of
`CorrectedJacquetCutFiltration` with the existing bundled
`Support.cutSupportQuotient` representations. It supplies linear equivalences
and a commuting square for every actual descended cut map. The source and
target are the actual normalized Jacquet modules and actual support images.

`cutCoordinateEquiv` compares the unbundled coordinate of `jacquetDiagram` with
the bundled `cutJacquetObject`. It is the identity after expanding the existing
carrier definitions. `cutCoordinateEquiv_map` identifies the original diagram
transition with `cutJacquetMap` under these equivalences. The support-membership
lemma compares the actual `correctedCoordinateSupport` condition with the
bundled corrected Jacquet support condition.

`cutCoordinateSupportEquiv` restricts the coordinate equivalence to upper
support. Its inverse uses the same support-membership equivalence. The lower
support pulled back to that upper support corresponds under this equivalence;
this is proved by reducing membership in a submodule preimage to membership of
the underlying value. Surjectivity then gives equality of the image of the
lower submodule with the bundled lower-in-upper submodule.

`cutCoordinateQuotientEquiv` is the induced linear equivalence of actual
quotients, constructed with `Submodule.Quotient.equiv`. Its value on a supported
representative is the existing bundled quotient projection of the supported
coordinate equivalence. Restricting the already proved actual cut-map square
gives the supported square. Quotient induction and the two representative
formulas then prove `cutCoordinateQuotientEquiv_map` for every quotient class.
This closes the bundled transition comparison left open by the earlier
filtration module.

The construction requires neither containment between the two chosen support
sets nor a rank restriction: both quotients use the pulled-back denominator.
The field and representation universes are independent, and rank zero and an
empty coordinate index set are retained. No graded geometric comparison,
exactness or effectivity conclusion is claimed here. The original signed
homogeneous differential is not changed; this result compares its coordinate
transition maps before forming signed sums. The provenance is internal, from
the existing actual carrier definitions, actual support preservation, and
ordinary linear equivalences and submodule quotients.
