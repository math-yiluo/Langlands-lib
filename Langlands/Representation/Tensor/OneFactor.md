# Tensor representations with one acting factor

This module contains the generic tensor-action declarations extracted unchanged
from `Langlands.Representation.Induction.BinaryProduct`. The public namespace
remains `Langlands.BinaryTensor`. Binary normalized induction imports this module,
and the partial-derivative tensor statement reuses the same first-factor
constructions. No induction or classification construction is imported here.

These declarations are in the namespace `Langlands.BinaryTensor`. Here `G` is a
group and all modules are complex vector spaces.

- `secondFactor V σ` is the representation `1 ⊗ σ` of `G` on `V ⊗ W`:
  `g (v ⊗ w) = v ⊗ σ(g) w` (`secondFactor_apply`, `secondFactor_tmul`). It is
  `Representation.tprod` of the trivial representation on `V` and `σ`.
- `firstFactor ρ W` is the representation `ρ ⊗ 1` of `G` on `V ⊗ W`:
  `g (v ⊗ w) = ρ(g) v ⊗ w` (`firstFactor_apply`, `firstFactor_tmul`).
- `secondFactorMap f g`, for a linear map `f : V → V'` and an intertwiner
  `g : σ → σ'`, is the intertwiner `f ⊗ g` from `secondFactor V σ` to
  `secondFactor V' σ'`. `secondFactorMap_tmul` and
  `secondFactorMap_toLinearMap` give its values. `secondFactorMap_id` and
  `secondFactorMap_comp` are the functor laws. `secondFactorMap_zero_left` and
  `secondFactorMap_zero_right` say that `f ⊗ g` is zero if `f = 0` or `g = 0`.
- `firstFactorMap f g`, for an intertwiner `f : ρ → ρ'` and a linear map
  `g : W → W'`, is the intertwiner `f ⊗ g` from `firstFactor ρ W` to
  `firstFactor ρ' W'`, with the corresponding lemmas `firstFactorMap_tmul`,
  `_toLinearMap`, `_id`, `_comp`, `_zero_left` and `_zero_right`.

The group and each carrier have independent universes. A topology is needed only
for the smoothness results; the vector spaces carry no topology and need not
have finite dimension.

`isSmooth_secondFactor` and `isSmooth_firstFactor` say that a smooth acting
factor gives a smooth tensor representation. A pure tensor is fixed by an open
subgroup fixing its acting coordinate. Tensor induction and closure of smooth
vectors under addition establish the result for every tensor.

The definitions use Mathlib's tensor representation, trivial representation and
tensor-product linear maps. The smoothness proofs use the Library's
`IsSmooth` predicate and `isSmoothVector_add`. All declaration bodies, hypotheses
and universe parameters are retained from the published binary-product module.
