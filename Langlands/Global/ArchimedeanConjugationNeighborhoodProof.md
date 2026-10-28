# Uniform compact conjugation near the identity

`Langlands.Global.ArchimedeanGL.compactConjugationNeighborhood` proves the
published `CompactConjugationNeighborhoodStatement K n` for an arbitrary
number field `K : Type u` and every natural rank `n`, including zero. It
uses the existing topology of `InfiniteAdelicGL K n` and the existing
subgroup `standardInfiniteCompact K n`.

Given an identity neighborhood `U`, the proof first obtains an identity
neighborhood on which every conjugation by the compact subgroup takes
values in `U`. For each fixed compact element `k`, continuity of the map
`(y, k) ↦ k*y*k⁻¹` at `(1, k)` gives the required eventual condition,
since its value there is the identity. The published theorem
`isCompact_standardInfiniteCompact` and Mathlib's
`IsCompact.eventually_forall_of_forall_eventually` make this condition
uniform over all elements of the subgroup.

The neighborhood characterization `mem_nhds_iff` supplies an open
identity neighborhood `V` inside that uniform condition. Taking `k = 1`
shows `V ⊆ U`. For any element of the compact conjugation saturation of
`V`, its witnesses `k` and `y ∈ V` give `k*y*k⁻¹ ∈ U` directly from the
same uniform condition. Thus this single `V`, chosen before `k` and `y`,
has all the properties required by the exact statement.

This is an internal topological proof from published subgroup compactness
and Mathlib's continuity and compactness API; no external literature
result is invoked. The imported statement and its dependencies are
unchanged. The theorem supplies neighborhood selection only.
Normalized kernels, compact conjugation averaging, convolution
approximation, compact-type preservation, reproduction and the final
automorphic differential-growth theorem remain separate obligations.
