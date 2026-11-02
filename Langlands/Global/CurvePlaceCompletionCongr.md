# Transport of actual curve-place completions

Author: Worker 208.

For fields `k`, `F` and `F'` in an arbitrary common universe, with their
specified `k`-algebra structures, this construction transports the concrete
`AlgebraicCurve.Place k F` and its actual adic completion along a specified
`k`-algebra equivalence `e : F ≃ₐ[k] F'`. It uses the published place
equivalence and its preservation of the normalized discrete order, then
extends the original field equivalence to the completions. It requires
neither a global-field hypothesis nor an assumed package of local maps.

`curvePlaceEquiv` reuses `AlgebraicCurve.Place.congrEquiv`.
`curvePlaceEquiv_valuation` proves exact equality of the normalized
valuations on `x` and `e x`. For nonzero elements, the equality of orders
gives equality of the logarithms of the valuations, and exponentiation
recovers the values. The zero case follows from the field equivalence.

`curvePlaceWithValEquiv` is the same field map on Mathlib's valued type
synonyms. The two uniform-continuity lemmas transfer each valuation
neighborhood radius, represented as a quotient of two nonzero values,
using the inverse map. Mathlib's completion functor gives
`curvePlaceValuedCompletionEquiv`; continuity of the completion map and
its inverse gives `curvePlaceValuedCompletionHomeomorph`.

The canonical adic-completion wrappers then give the ring equivalence
`curvePlaceCompletionCongr` and the homeomorphism
`curvePlaceCompletionHomeomorph` with the same underlying function. The
topologies are the existing completion topologies. The identity
`curvePlaceCompletionCongr_algebraMap` says that the comparison sends
the canonical image of each `x : F` to the canonical image of `e x`.
Combining this identity with `e.commutes` gives
`curvePlaceCompletionAlgEquiv`, whose underlying ring equivalence is the
same map and which respects the specified constant field `k`.

`curvePlaceValuedCompletionEquiv_le_one_iff` proves preservation of the
closed unit ball. The unit balls in both valued completions are clopen.
The set on which their membership predicates agree is closed in the source
completion, using the homeomorphism and the clopen predicates. Completion
induction therefore reduces the assertion to field elements, where it is
the exact normalized valuation equality already proved. This yields
`curvePlaceCompletionCongr_mem_integers_iff` on the actual adic
completions. Restricting the ring equivalence and its inverse constructs
`curvePlaceCompletionIntegersCongr`; the coercion formula identifies it
with the original comparison. Restricting the continuous maps constructs
`curvePlaceCompletionIntegersHomeomorph` for the existing subspace
topologies.

This is derived infrastructure for presentation independence of the
adelic local factors in Brian Conrad, *Weil and Grothendieck approaches
to adelic points*, December 31, 2011, printed p.1 and pp.6–8. Registered
source `conrad-2011-weil-grothendieck-adelic-points`, SHA-256
`fe4a9193aff4ef575665b40971f3da32f850a74d87b3f2d0fa28bba26b9cbabb`.
The imported Library place transport supplies the underlying arithmetic
comparison; the completion extension is internal derived content.

The comparison depends on a specified field equivalence. It does not
assert invariance under an arbitrary change of the constant field.
Identification with the conventional places of a global function field,
finite poles, the full-field adelic diagonal, the induced comparison of
restricted products, and its identity and composition laws remain separate
obligations. This local construction makes no claim to establish those
results or the whole-paper geometric assertions.
