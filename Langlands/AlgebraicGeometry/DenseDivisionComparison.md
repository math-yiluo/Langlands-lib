# Comparing dense charts of schemes with invertible translations

`InvertibleTranslations` packages a total multiplication over a base together
with isomorphisms `(x,y) ↦ (x,xy)` and `(x,y) ↦ (xy,y)`. For a group scheme
these are the usual translations, with inverses given by multiplication against
the inverse coordinate. The inverse of the right translation defines `chartDiv`
on pairs `(a,b)` from a chart by taking the unique `x` such that `xb = a`.

`exists_iso_of_chart` compares two smooth separated schemes over a reduced,
locally Noetherian, quasi-compact base. Their common chart has fibre-dense open
immersions into both schemes. It suffices that their multiplications agree on
triples in the chart in the direction stated. The two chart division maps are
smooth because they factor as an open immersion, a translation isomorphism,
and a smooth projection. For surjectivity, fix a first coordinate `x`. The
conditions that `b` and `xb` lie in the chart define dense opens of that fibre
by pullback of fibre density and the left translation. A point in their
intersection gives a pair in the chart product whose division is `x`.

The first scheme is quasi-compact over the base, so the chart product is
Noetherian and both division maps are quasi-compact. Compatibility of the
multiplications shows that for a first division value lying in the chart, the
second division has the same chart value. Applying
`exists_iso_of_agrees_over_dense_open` gives the comparison isomorphism.

This is the common-chart descent argument of Bosch, Lütkebohmert and Raynaud,
*Néron Models* (1990), §5.1 Proposition 3 and Lemma 4, printed pp. 113–114
(PDF pp. 120–121), expressed with right division. The literature ID is
`bosch-lutkebohmert-raynaud-1990-neron-models`, and the retained file SHA-256 is
`16d0701b4192ae9db91d083c1df69c0492b00a994aee7bcb0abca365d859d529`.
