# Extended labels as supported polynomial towers

This internal auxiliary module implements the label data conversion in Lemma
`lem:BKlabels` of the operator’s numerical local Langlands route note
(`operator-numerical-llc-route-2026-11-16`). It uses the Library encoding of
Bushnell–Kutzko (1994), (1.13) and (3.7).

`extendedLabelsEquiv` identifies an extended label of final ramification
index one with its descending positive levels and a polynomial tower. The
level-zero polynomial occupies the last slot of the tower. Its degree is
`f / p.d`, so the product of the degrees is `f`. The preceding degree products
give the coefficient-field exponents, including `p.d` for the final slot.

The proof constructs the label from the support and tower. It computes each
ramification index by taking the gcd of `a` and the levels through that
position. Induction on the position gives the same recurrence as the label
definition. At the last position the gcd is one by the support condition.
Injectivity follows by recovering the levels, degrees and polynomial entries.
For surjectivity the published label constraints give these data with the
required degree products, and the equality of coefficient-field exponents
allows each polynomial to be placed in its prescribed field.
