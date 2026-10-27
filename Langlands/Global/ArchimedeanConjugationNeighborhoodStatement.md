# Uniform neighborhood selection for compact conjugation

`Langlands.Global.ArchimedeanGL.CompactConjugationNeighborhoodStatement K n`
is a topological prerequisite for localized compact conjugation averaging.
It retains an arbitrary number field `K : Type u` and every natural rank `n`,
including zero. The ambient group is the existing `InfiniteAdelicGL K n`,
with its original topology, and the compact subgroup is the existing
`standardInfiniteCompact K n`.

For every neighborhood `U` of the identity, the proposition asks for an
open identity neighborhood `V` contained in `U` such that

```text
{ k y k⁻¹ | k in standardInfiniteCompact K n, y in V } ⊆ U.
```

The quantifiers choose `V` before all compact elements and all points of
`V`. No openness or conjugation invariance is required of the supplied
`U`; conjugation invariance is also not asserted of `V`.

This is a source-free internal statement obtained from continuity of
conjugation and compactness of the published subgroup. A prospective proof
applies Mathlib's `IsCompact.eventually_forall_of_forall_eventually` to the
map `(y, k) ↦ k*y*k⁻¹` at `(1, k)`, then takes an open neighborhood inside
the resulting uniform neighborhood. That argument remains a separate proof
obligation; this module defines only the proposition.

The orientation of the displayed saturation agrees with the support bound
in `CompactKernelConjugationAverageStatement`: the average evaluates its
input at `k⁻¹*x*k`, so its possible nonzero points have the form `k*y*k⁻¹`.
If an input kernel has closed support in `V`, its compact conjugation
saturation is consequently contained in `U`. This is only a description of
how the target is intended to be used; the present module constructs no
kernel or average and imports no averaging proof.

The proposition requires no Haar measure, measurable-space structure,
positive-rank restriction, maximality assumption, smoothness certificate,
approximate identity or reproducing kernel. Normalized-kernel existence,
smooth compact averaging, derivative-topology approximation, compact-type
preservation, reproduction and automorphic differential growth remain
separate obligations.
