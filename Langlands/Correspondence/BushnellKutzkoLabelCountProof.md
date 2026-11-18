# Counting Bushnell–Kutzko labels by polar parts

`Langlands.Henniart.bushnellKutzkoLabelCount` proves
`Langlands.Henniart.BushnellKutzkoLabelCountStatement`. This is the count in
Lemma `lem:BKlabels` of the numerical local Langlands route note, registered
as `operator-numerical-llc-route-2026-11-16`. The label sets come from
Bushnell–Kutzko (1994), (1.13) and (3.7) for positive level and printed
page 126 for level zero.

For positive `m`, `extendedLabelsEquiv` writes a label with `e(p) = 1` as
its descending positive levels and a polynomial tower with a final stage
for the polynomial at level zero. The positive levels include `m`. The
label recurrence for `e(p)` gives the support gcd, and the polynomial
degrees multiply to `f`. Divisibility and positivity of `f` give the
hypothesis `0 < n / f` for this equivalence.

On the polar-part side, `polarPartsEquiv` lists the coefficients at those
same ordered levels, followed by the nonzero constant coefficient. The
tuple generates the degree-`f` field. For each sequence of polynomial labels,
the product of the numbers of successive root choices is `f`, which gives
`generatingTupleEquiv`. A Galois automorphism fixing all coefficients fixes
their generated field, so each orbit also has size `f`. The lemma
`encard_eq_polarPartCount_of_equiv` cancels this common factor and unfolds
`polarPartCount` using `labelFieldSize q = q` and `(f * m) / f = m`.

At level zero the coefficients form a generating nonzero one-tuple in the
degree-`n` field. A polynomial tower of one stage consists of a monic
irreducible polynomial of degree `n` other than `X`. The lemma
`degenerateLabelSet_encard` compares these polynomials with the published
Galois orbit count using the common factor `n`.
