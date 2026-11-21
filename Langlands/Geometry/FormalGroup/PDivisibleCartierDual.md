# The actual Cartier dual tower of a p-divisible group

`PDivisibleGroup.dualInclusions` applies finite Cartier duality at every
level, with inclusions given by the duals of the original transfers.
`PDivisibleGroup.dual` takes the stated finite Cartier exactness theorem as
an explicit hypothesis. It uses the duals of the original inclusions as
transfers. Functoriality is contravariant, and dualizing multiplication by
`p^(n-m)` gives multiplication by the same integer. Exactness follows by
reversing the short exact sequence with the two exponents interchanged.

This constructs the dual tower described by Tate, *p-Divisible Groups*
(1967), §2.3, printed p. 166 (PDF p. 5), from the actual finite spectra and
maps. Its exactness input is Tate's theorem on the dual of the sequence in
§1.3, printed pp. 159–160 (PDF pp. 1–2). The construction retains all points
of the finite dual schemes, including those on an étale factor.
