# Compatible real or complex structure on the actual infinite completion

Author: Worker 1359.

This internal derived construction places a compatible `RCLike` structure
on the actual infinite-place completion of a field in arbitrary universe.
It retains the given normed field structure. In particular, it leaves
the existing completion carrier, field operations, norm, metric, uniform
structure and topology unchanged.

`Langlands.Analytic.rclikeOfNormPreservingRingEquiv` starts from a complete
normed field `K`, an `RCLike` field `k` in an independent universe, and
a ring equivalence `e : K ≃+* k` which preserves the given norms. It
pulls back the real algebra map, complex conjugation, real and imaginary
parts, the distinguished imaginary unit and the partial order. It uses
the original `NormedField K` and `CompleteSpace K` fields in the resulting
structure. Density of the norm follows by pulling a witness back from
`k`; compatibility of real scalar multiplication with the norm follows
by applying `e` and the scalar norm equality in `k`. The remaining
`RCLike` identities follow by applying `e`, its injectivity, and the
identities in `k`.

`isRCLikeNormedField_of_ringEquiv` packages this construction as Mathlib's
proposition `IsRCLikeNormedField K`. Its compatibility equality is
reflexivity: the new structure's normed field is definitionally the
original one. A consumer may install the associated `RCLike` structure
locally with `IsRCLikeNormedField.rclike K`.

`NumberField.InfinitePlace.completion_isRCLikeNormedField` applies the
generic construction to each actual `v.Completion`. Mathlib proves that
every infinite place is real or complex and provides the corresponding
ring equivalence to `ℝ` or `ℂ`, with its isometry proof. These isometries
give the required norm identities. No `NumberField F` hypothesis is
needed beyond `Field F` and the actual infinite place.

The provenance is the existing Mathlib infinite-place completion
equivalences, the `RCLike` structure laws and explicit structure
transport. This is an analytic comparison prerequisite only. It
constructs no maximal compact subgroup and proves no parabolic product
coverage or general Iwasawa existence theorem.
