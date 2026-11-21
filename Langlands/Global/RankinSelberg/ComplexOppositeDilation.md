# Diagonal contraction on the complex opposite cell

For a positive real parameter ε, let the entries of the diagonal matrix be
ε^i in rank n, starting with i = 0. Conjugation by this matrix on the lower
unipotent corresponds under transpose to conjugation by its inverse on the
upper unipotent. The latter multiplies each strict upper entry (i, j) by
ε^(j−i). Each entry is a two-dimensional real vector space, so the product
Lebesgue measure has Jacobian ε^D, where D is the sum of 2(j−i) over the
strict upper entries. The pushforward of the measure therefore has density
ε^(−D) against the original measure. The Lean proof computes the scalar Haar
change in each complex entry, takes the product on measurable rectangles, and
transports it through the upper-entry homeomorphism.

For ε at most one, each strictly upper entry has new norm at most ε times
its original norm, since j−i is a positive integer. The diagonal entries stay equal
to one, and the opposite off-diagonal entries stay zero. Taking the
entrywise maximum gives the asserted displacement from the identity after
transpose. The empty product and sum also give the formulas in rank zero.

This is an internal change of variables for the compact integral in
`ComplexModulusOpenCell`. It uses the complex matrix integration setting of
Jacquet, *Archimedean Rankin–Selberg Integrals* (2009), §4.
