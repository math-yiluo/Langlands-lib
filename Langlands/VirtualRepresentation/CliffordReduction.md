# Clifford reduction to representations that are scalar on a commutative normal subgroup

Helper module for the proof of
`Langlands.ClassField.Global.RelativeWeilGroup.InducedCharacterGenerationStatement`.
It provides the Clifford step sketched in item 3 of "Relation to the source" in
the Markdown of the statement module. It does not decompose an irreducible
representation. Instead it gives an injective intertwiner, which needs no
semisimplicity:

`Ind_S^G W ↪ A`, `f ↦ Σ_{q ∈ S\G} ρ(q⁻¹) f(q)`.

Here `N` is a normal subgroup of `G`, `χ : N → ℂ` is a function (an eigenvalue
function), `W` is the simultaneous eigenspace of `N` for `χ`, and `S` is the
stabilizer of `χ`. All declarations are in the namespace
`Langlands.VirtualRepresentation.Clifford`. The group need not be topological.

## Stabilizer and eigenspace

- `conjN N g n = g n g⁻¹ ∈ N`, with `conjN_coe`, `conjN_mul` and `conjN_one`.
- `weightStabilizer N χ` is the subgroup of `g` with `χ (g n g⁻¹) = χ n` for all
  `n : N`. `le_weightStabilizer`: if `N` is commutative then
  `N ≤ weightStabilizer N χ`.
- `weightSpace N ρ χ` is the published `LieKolchin.weightSpace` of `ρ`
  restricted to `N`: the vectors `w` with `ρ n w = χ n • w` for all `n : N`
  (`mem_weightSpace`).
- `apply_mem_weightSpace`: the stabilizer preserves the eigenspace.
  `inv_apply_mem_weightSpace`: `ρ(g⁻¹)` carries the eigenspace of `χ` into the
  eigenspace of `n ↦ χ (g n g⁻¹)`.
- `weightRep N ρ χ` is the representation of the stabilizer on the eigenspace,
  by restriction. `weightRep_scalar`: an element of `N` acts on it by the scalar
  `χ n`.

## Right cosets

`coset_out_mul_mul_inv` and `cosetsMulRight S g`: right multiplication by `g` is
a bijection of the published right-coset type `Induction.Cosets S`, given by
`q ↦ coset (q.out * g)`.

## The intertwiner

Assume that the stabilizer has finite index.

- `cliffordLinearMap N ρ χ` is the linear map
  `f ↦ Σ_q ρ (q.out)⁻¹ (f q.out)` from Mathlib's coinduced space (the published
  model of `FiniteRepresentation.induce`) to `V`.
- `cliffordLinearMap_intertwining`: the map is `G`-equivariant. For each coset
  `q`, write `q.out * g` as `factor · out'` with `out'` the representative of its
  coset (the published `Induction.factor_mul_out`). The term for `q` in the sum
  for `g · f` is the term for `cosetsMulRight S g q` in `ρ g (Ψ f)`. The sum is
  then reindexed by the bijection (`Equiv.sum_comp`). `cliffordMap` is the
  resulting intertwiner.
- `conj_weight_injective`: distinct right cosets `q` give distinct eigenvalue
  functions `n ↦ χ (q.out n q.out⁻¹)`. Equal functions force
  `q₁.out * q₂.out⁻¹ ∈ S`, i.e. equal cosets.
- `cliffordMap_injective` (for finite-dimensional `V`): the summand for `q`
  lies in the eigenspace of the `q`-th function. The published
  `LieKolchin.iSupIndep_weightSpace` says that eigenspaces of distinct
  functions are independent. With Mathlib's
  `iSupIndep_iff_finsetSum_eq_zero_imp_eq_zero`, a vanishing sum has vanishing
  summands. Hence `f (q.out) = 0` for every coset. Then `f = 0`, because the
  published coset coordinates `Induction.coordinates` are injective.

## Dependencies

The module imports the published `Langlands.VirtualRepresentation.ExactInduction`,
`Langlands.Weil.Representation.SubquotientContinuity`,
`Langlands.Weil.Representation.InductionContinuity` and
`Langlands.Group.LieKolchin.CommonEigenvector` (`weightSpace`,
`iSupIndep_weightSpace`).
