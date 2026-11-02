# Kernel pair and recognition of the canonical etale quotient

This internal helper proves two facts about the canonical etale quotient of
`SmoothRelationQuotientStatement`: the arrow space is the kernel pair of the
fixed quotient map, and the quotient is identified with any etale sheaf that
has a compatible presentation by a scheme. It uses only the equivalence-relation
witness. It does not use smoothness, an atlas of the arrow space, or any
geometric conclusion of the quotient theorem. Its provenance is the sheaf
condition of algebraic spaces and schemes for the big etale topology, Mathlib's
local injectivity of the sheafification unit, and the Library comparison
`commonEtalePresentationIso`.

Fix a scheme `S`, a scheme `U` over `S`, an algebraic space `R` over `S`, endpoint
maps `s t : R.presheaf ⟶ (schemeYoneda S).obj U` and the full sectionwise
monomorphic equivalence-relation witness `h : IsEquivalenceRelation R s t`. The
quotient `quotientSheaf R s t h` is the etale sheafification of the presheaf of
pointwise classes. The map `quotientMap R s t h` is the class map followed by the
sheafification unit. All test schemes are arbitrary schemes over `S`, in
universe `u`.

## Sheaf conditions

`isSheaf_etale_presheaf` and `isSheaf_etale_schemeYoneda` restate that the
underlying presheaf of an algebraic space and the lifted functor of points of a
scheme over `S` are sheaves of types for the big etale topology. Both are fppf
sheaves, and the etale topology on `Over S` is coarser than the fppf topology
(`Sites.etaleTopologyOver_le_fppfTopologyOver`).

## Kernel pair

`relation_of_quotientMap_eq` is the key step. Let `x` and `y` be points of `U`
over a test scheme `T` with the same image in the etale quotient. The
sheafification unit is locally injective, so the classes of `x` and `y` agree on
a covering sieve of `T`. On each arrow of this sieve the two restricted points
are related by an arrow section of `R`, chosen arbitrarily. These choices are
compatible: endpoint pairs of `R` determine sections, and both choices have the
same restricted endpoints on every overlap. The etale sheaf property of `R`
glues them to one section `r` over `T`. The separatedness of the functor of
points of `U` gives `s r = x` and `t r = y`, because these hold on the covering
sieve.

`quotientMap_eq_iff` states that two points over any test scheme have the same
image in the etale quotient exactly when they are related by an actual arrow
section of `R`. The converse direction holds because the class map already
identifies the two endpoints of every arrow.

`isPullback_quotientMap` proves that the square with `R.presheaf` at the top
left, `s` and `t` to the functor of points of `U`, and `quotientMap R s t h` on
both remaining sides is a pullback of presheaves. At every test scheme the
square commutes by `quotientMap_eq_iff`. Arrow sections are determined by their
endpoint pairs, by the injectivity part of `h`. Every pair of points with equal
quotient images comes from an arrow section, by `quotientMap_eq_iff`. The Mathlib
pointwise pullback criterion for types and the evaluation criterion for functor
categories give the pullback. This is the kernel-pair conclusion of
`SmoothRelationQuotientStatement`.

`isLocallySurjective_quotientMap` states that `quotientMap R s t h` is locally
surjective for the big etale topology: the class map is surjective on every
section type, and the sheafification unit is locally surjective.

## Recognition of the quotient

`quotientSheafIsoOfPresentation` constructs an isomorphism from the canonical
etale quotient to an etale sheaf `F`, from the following data. There are a
scheme `W` over `S` and maps `g` from the functor of points of `W` to that of
`U` and `b` from the functor of points of `W` to `F`. The composite of `g` with
`quotientMap R s t h` must be locally surjective for the etale topology, and so
must `b`. For every test scheme `T` and morphisms `x y : T ⟶ W`, the images of
`x` and `y` under `b` must agree exactly when the points `g x` and `g y` of `U`
are related by an arrow section of `R`. By `quotientMap_eq_iff` the two
presentations of the quotient and of `F` by `W` then have the same kernel. The
Library comparison `commonEtalePresentationIso` gives the isomorphism.
`quotientSheafIsoOfPresentation_hom_fac` states that the composite of `g`,
`quotientMap R s t h` and the isomorphism equals `b`.

The intended use is a scheme `W` that slices the relation, with `b` the
presentation of an algebraic-space quotient of the relation restricted to `W`.
This file does not prove that such a presentation exists.
