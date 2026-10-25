# Smooth vectors are fixed by a reference tail

This module is an internal corollary of the topological construction in
`GroupTopology` and the published `Langlands.IsSmoothVector` and
`Langlands.IsSmooth` definitions. It does not transcribe a separate source
theorem.

Let `H i` be open subgroups of the local groups `G i`, and let `ρ` be a
representation of the actual cofinite restricted product over a commutative
ring `R`. The ring, index type, local groups, and representation carrier have
independent universes `uR`, `uI`, `uG`, and `uV`.

`exists_tailReferenceSubgroup_fixed_of_isSmoothVector` proves that a smooth
vector `v` is fixed by `tailReferenceSubgroup H S` for some finite set `S`.
By the definition of smoothness there is an open subgroup fixing `v`.
`exists_tailReferenceSubgroup_le` supplies a tail subgroup contained in that
open subgroup, and the fixed-vector law restricts to the tail.

`exists_tail_fixed_of_isSmooth` applies this result to each vector of a smooth
representation and exposes the coordinate form needed by callers:

```text
∀ v, ∃ S : Finset ι, ∀ g : RestrictedGroup G H,
  (∀ i ∈ S, g i = 1) →
  (∀ i ∉ S, g i ∈ H i) →
  ρ g v = v.
```

There is no topology on the representation carrier and no dimension,
admissibility, irreducibility, countability, compactness, or nonemptiness
hypothesis. The result also applies to compact open reference subgroups.
The proof requires only openness for tail extraction; it makes no assertion
that a tail subgroup is itself open.
