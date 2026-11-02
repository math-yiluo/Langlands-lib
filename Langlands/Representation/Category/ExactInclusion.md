# Exact inclusion of smooth representations

This internal construction derives exactness of the existing full-subcategory
inclusion `Langlands.SmoothRep.toRep` from the closure results in
`Langlands.Representation.Category.Abelian`. It introduces no new notion of
smoothness and no assumptions about taking the smooth part of an arbitrary
representation.

The ring `R`, group `G` and representation carriers have independent universes
`uR`, `uG` and `uV`. The coefficient ring is commutative. The group has a topology;
these results do not require continuity of multiplication or inversion.
The source is the full category of representations whose vectors are fixed by
open subgroups, and the target is Mathlib's category `Rep R G`.

`toRep_preservesFiniteLimits` uses the proved closure under subobjects to obtain
preservation of kernels from Mathlib's
`ObjectProperty.preservesKernels_ι`. The inclusion is additive. Mathlib's
`Functor.preservesFiniteLimits_of_preservesKernels` then supplies preservation of
all finite limits.

`toRep_preservesFiniteColimits` uses closure under quotients and
`ObjectProperty.preservesCokernels_ι` in the same way, followed by
`Functor.preservesFiniteColimits_of_preservesCokernels`. Both source and target
are the existing abelian categories, so the finite products, coproducts and
equalizers needed by these reductions already exist.

Thus homology of a complex in the smooth category can be compared with homology
of its underlying algebraic representation complex by the usual exact-functor
homology comparison. This is exactness of the inclusion, with no assertion that
the right adjoint taking smooth vectors is exact.
