# A specialization chain from Krull dimension at least two

Author: Worker 919.

Module `Langlands.AlgebraicGeometry.KrullDimensionChain`. This is an internal supporting unit
for Task 7586, with no literature source.

## Statement

```
theorem exists_chain_of_not_le_one {X : Scheme.{u}} [CompactSpace X]
    (h : ¬ topologicalKrullDim X ≤ 1) :
    ∃ y₀ y₁ z : X, y₀ ⤳ y₁ ∧ y₁ ⤳ z ∧ y₀ ≠ y₁ ∧ y₁ ≠ z ∧ IsClosed ({z} : Set X)
```

A quasi-compact scheme of topological Krull dimension greater than one has a chain
`y₀ ⤳ y₁ ⤳ z` of two proper specializations that ends at a closed point.

## The implemented proof

`topologicalKrullDim X` is the Krull dimension of the poset of irreducible closed subsets.
By `Order.krullDim_le_one_iff`, some irreducible closed `B` is neither minimal nor maximal.
So there are irreducible closed sets `A < B < C`. Schemes are quasi-sober, so these sets have
generic points (`IsIrreducible.isGenericPoint_genericPoint`). Take `y₀` the generic point of
`C` and `y₁` that of `B`. The closed set `A` is compact in the compact T₀ space `X`, so it
contains a closed point `z` (`IsClosed.exists_closed_singleton`).

- `y₀ ⤳ y₁` because `y₁ ∈ B ⊆ C`, and `y₁ ⤳ z` because `z ∈ A ⊆ B`
  (`IsGenericPoint.specializes_iff_mem`).
- If `y₀ = y₁`, then `C = closure {y₀} = B`, which contradicts `B < C`.
- If `y₁ = z`, then `B = closure {z} = {z} ⊆ A`, which contradicts `A < B`.
