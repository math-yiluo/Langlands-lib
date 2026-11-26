# Idempotent patching over the adele ring

`exists_adele_idempotent_patch` takes a finite family `d i` that generates the unit ideal of
`Adeles K`. It gives orthogonal idempotents `e i` summing to one such that `∑ i, e i * d i`
is a unit of the full adele ring.

A Bézout relation shows that at each place some entry is nonzero. At almost all finite places,
the entries and the coefficients of the relation are integral. If all entries had valuation
strictly below one at one of these places, the valuation inequality for a sum would put the
value of one strictly below one. Thus at almost every finite place an entry has valuation
one. Choose a nonzero entry at each place, preferring an entry of valuation one at every
finite place where one exists. Its index defines the indicator idempotents, whose finite
coordinates are all integral. The patched adele is nonzero in every completion and has
valuation one at almost all finite places. `NumberField.AdeleRing.isUnit_iff` gives its
invertibility.

The argument uses the restricted-product definition of the full adele ring and the usual
criterion for an idele, as in Getz and Hahn, *An Introduction to Automorphic Representations*
(2024), §§2.1–2.2.
