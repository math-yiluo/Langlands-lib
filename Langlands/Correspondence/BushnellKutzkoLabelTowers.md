# Finite-field towers for the Bushnell–Kutzko label count

This internal auxiliary module implements the root-tuple argument in Lemma
`lem:BKlabels` of the operator’s numerical local Langlands route note
(`operator-numerical-llc-route-2026-11-16`). The successive fields are the
coefficient fields of the polynomial labels in Bushnell–Kutzko (1994), (1.13)
and (3.7).

`DegreeProfile` records positive successive degrees with product `f`.
`PolynomialTowers` attaches a monic irreducible polynomial other than `X` at
each stage. Its coefficient field has degree over the base field equal to the
product of the earlier degrees.

The proof of `generatingTupleEquiv` identifies the degree of the field generated
by a prefix with the product of the relative minimal-polynomial degrees. Each
field in the prescribed profile embeds into the ambient degree-`f` field
because its degree divides `f`. Its image is the unique intermediate field of
that degree. This identifies the root choices at different stages with
independent choices over the prescribed fields. An irreducible polynomial of
degree `d` splits into `d` distinct roots in the ambient field when `d` divides
the degree of that field over the coefficient field. The product of the numbers
of choices is `f`, so the resulting equivalence has a factor `Fin f`. The
embeddings and the enumeration of the roots use classical choice.
