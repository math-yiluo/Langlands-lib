# Coordinates for a finite permutation basis

Worker 1550. This internal construction relates coordinate functions on a finite
set to a representation with a permuted basis. It is derived from the published
basis and representation APIs and `Langlands.PermutationBasis.indexAction`.
There is no external mathematical source or additional classification premise.

For a commutative ring `R`, a group `Γ`, an `R`-module `V`, a basis
`b : Module.Basis I R V`, and an equivalence `e : J ≃ I` with `J` finite,
`coordinateEquiv b e : (J → R) ≃ₗ[R] V` is the inverse coordinate map for the
basis `b.reindex e.symm`. With a finite enumeration of `J`,
`coordinateEquiv_apply` identifies it with the sum `∑ j, m j • b (e j)`.
The equivalence itself needs only `Finite J` and does not choose an enumeration
as an extra input.

`equivFun_symm_equivariant` considers a representation `ρ` on `V` and a
permutation homomorphism `a : Γ →* Equiv.Perm I` satisfying
`ρ g (b i) = b (a g i)`. When `I` is finite, it proves

```
b.equivFun.symm (fun i => m (a g⁻¹ i)) = ρ g (b.equivFun.symm m).
```

The proof expands both inverse coordinate maps as finite sums, applies
linearity and the stated basis permutation, and reindexes the sum by `a g`.
The group homomorphism law gives `a g⁻¹ (a g i) = i`.

`coordinateEquiv_equivariant` applies this identity to the reindexed basis.
For `a : Γ →* Equiv.Perm J`, it assumes
`ρ g (b (e j)) = b (e (a g j))` and proves

```
coordinateEquiv b e (fun j => m (a g⁻¹ j)) =
  ρ g (coordinateEquiv b e m).
```

`coordinateEquiv_equivariant_of_permuted` specializes to the index action
canonically induced by setwise preservation of a basis. It assumes `R`
nontrivial, `hb : ∀ g i, ∃ i', ρ g (b i) = b i'`, and
`e (a g j) = indexAction ρ b hb g (e j)`. The canonical basis-action equation
then supplies the preceding theorem's hypothesis. All types have independent
universes. Empty finite coordinate sets are allowed; the proofs use no chosen
basis index or positive-rank hypothesis.

This helper supplies the coordinate equivalence used to match the finite-orbit
model with the actual character lattice in the induced-torus Weil decomposition.
It makes no assertion about group-scheme isomorphisms or descent.
