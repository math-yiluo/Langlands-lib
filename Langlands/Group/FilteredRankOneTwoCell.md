# Group algebra for a filtered rank-one two-cell decomposition

This internal derived module works in an arbitrary group `G`. Worker 1600
is the author. It defines `FilteredRankOne.reflectionCell U Z m` as the
literal set product `U {m} Z U` for subgroups `U` and `Z`.

The theorem `coe_sup_eq_twoCell` identifies the subgroup `U ⊔ V ⊔ Z`
with `B ∪ U {m} Z U`, under these explicit inputs:

- `Vplus ≤ V`, and the subgroup `B` has carrier `Vplus Z U`;
- `m ∈ U ⊔ V ⊔ Z` and `m² ∈ Z`;
- conjugation by every element of `Z` sends `U` into `U`;
- inverse conjugation by `m` sends `Z` into `Z`, `U` into `V`,
  and `V` into `U`;
- `V ⊆ Vplus ∪ U {m} Z U`.

Because `B` is a subgroup, inverting its displayed factorization gives
the reverse order `U Z Vplus`; `exists_reverse_factors` records that
deduction. The reflection cell is stable under right multiplication by
`U` and `Z`. Left multiplication by `U Z` preserves it as well, using
the two stated conjugation assumptions.

Right multiplication of `B` by `m` lies in the reflection cell, by the
reverse factorization and inverse conjugation. Right multiplication of
the reflection cell by `m` lies in `U Z V`, using `m² ∈ Z`. Splitting
the last factor by the displayed assumption on `V` then gives a point
of `B` or the reflection cell. Stability under `m⁻¹` follows from
stability under `m` and `Z`. Inverse conjugation of `V` into `U` gives
right stability under `V`. The subgroup closure induction on `U`, `V`
and `Z` proves the required containment; the opposite containment uses
the supplied membership of `m`.

This is group algebra for the proof of the filtered rank-one
decomposition. It does not construct the subgroups from building data
or prove any filtration, base-cell group, conjugation, centralizer-zero,
or opposite-pair existence input. All such inputs remain hypotheses
of this generic intermediate result.
