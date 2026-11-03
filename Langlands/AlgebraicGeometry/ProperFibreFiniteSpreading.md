# Spreading finiteness from one fibre of a proper family

This internal geometric construction supports fixed-bundle ampleness spreading.
It works over schemes in any universe and does not assume flatness,
noetherianity, reducedness, or that the specified base point is closed.

For morphisms `f : X ⟶ Y` and `g : Y ⟶ S`, `baseFibreMap f g s`
is the actual map from the scheme-theoretic fibre of `f ≫ g` at `s`
to the fibre of `g` at `s`, obtained from the categorical pullback.
Its composite with the latter fibre inclusion is the former fibre
inclusion followed by `f`.

The first lemma uses universal closedness: the complement of the image
of the complement of an open containing the entire fibre is an open
neighbourhood of `s`. An affine neighbourhood inside it has its entire
inverse image in the given open.

Apply this to the quasi-finite locus of `f`. If `f ≫ g` is proper and
`g` is separated, then `f` is proper. When every point over `s` lies in
that quasi-finite locus, shrinking the base makes the restricted `f`
locally quasi-finite. A proper locally quasi-finite morphism is finite.

If `baseFibreMap f g s` is finite, then each fibre of `f` over a point
of `Y` above `s` is finite as a set. The proof lifts each such point
through the homeomorphism between a scheme-theoretic fibre and the
set-theoretic fibre, and identifies its inverse image using injectivity
of the fibre inclusion. The criterion for quasi-finiteness at a point
in terms of openness of its singleton in the fibre then supplies the
preceding hypothesis.

The provenance is internal: these arguments combine Mathlib's actual
scheme-theoretic fibres, the open quasi-finite locus, universal
closedness of proper morphisms, and
`IsFinite.of_isProper_of_locallyQuasiFinite` from
`Mathlib.AlgebraicGeometry.ZariskisMainTheorem`. This file does not prove
the fixed-bundle ampleness spreading proposition.
