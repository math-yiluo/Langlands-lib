# Injectivity of a base-changed linear map, tested on finite independent families

Faltings' proof of Stacks, More on Algebra, Proposition 15.36.1 (07E5), (2) ⇒ (4), starts with
"Let `a₁, …, a_n ∈ k` be elements such that `da₁, …, da_n` are linearly independent". This module
supplies the linear algebra that reduces injectivity of `K ⊗_k Ω_k → K ⊗_A Ω_A` to such finite
families. All declarations live in `Langlands.CommutativeAlgebra.Popescu.Faltings`.

## `injective_of_basis`

Let `g : M → N` be a linear map of vector spaces and `B` a basis of `M`. If `g ∘ B` is linearly
independent, then `g` is injective.

Proof: write `x` as a linear combination of `B` (`Basis.linearCombination_repr`), apply `g`
(`Finsupp.apply_linearCombination`), and use `linearIndependent_iff` to conclude that the
coordinates vanish.

## `liftBaseChange_injective_of_finite`

Setting:
- `K/k` is a field extension;
- `V` is a `k`-vector space with a spanning set `S`;
- `W` is a `K`-vector space that is also a `k`-vector space compatibly (`IsScalarTower k K W`);
- `f : V → W` is `k`-linear.

Assume that for every `n` and every `k`-linearly independent family `v : Fin n → V` with values in
`S`, the family `f ∘ v` is `K`-linearly independent. Then `K ⊗_k V → W`, `c ⊗ v ↦ c • f v`, is
injective.

Proof:
1. Choose a basis `B` of `V` contained in `S` (`exists_linearIndependent`, `Basis.mk`).
2. `B` base-changes to a `K`-basis `1 ⊗ B` of `K ⊗_k V` (`Basis.baseChange`). The map sends it to
   `f ∘ B`.
3. `f ∘ B` is `K`-linearly independent: it suffices to check finite subfamilies
   (`linearIndependent_iff_finset_linearIndependent`). Each finite subfamily is reindexed by
   `Fin n`, which is the hypothesis.
4. `injective_of_basis` concludes.
