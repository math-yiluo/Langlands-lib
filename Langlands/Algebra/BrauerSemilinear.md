# Semilinear transport of splitting and Brauer periods

`tensorSemilinearEquiv` tensors two ring equivalences that intertwine
the actions of their base fields through one field equivalence. The
underlying semilinear map is the usual tensor equivalence, and its
multiplicativity follows on pure tensors and then by additivity.

`isSplit_iff_of_semilinear` transports a matrix chart through a
semilinear ring equivalence by applying the field equivalence entrywise
to matrices. The inverse equivalences give the converse. Applying this
transport to each tensor power gives
`nsmul_classOf_eq_zero_iff_of_semilinear`, which compares vanishing of
the same multiple of the two Brauer classes. The base fields can live
in independent universes, and each central simple algebra shares the
universe of its base field.
