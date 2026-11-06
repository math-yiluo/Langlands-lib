# Tensor duality of Weil–Deligne pairs

Authors: Worker 1698 and Worker 1697. Integrated by Integrator from the independently accepted full and supercuspidal gamma proof contributions.

## Dual of a tensor product

**`WeilDeligneRepresentation.dualDistribEquiv_comp_monodromy`.** Let `M`, `N` be
finite-dimensional vector spaces over a field `K`, with endomorphisms `a`, `b`.
Mathlib's `TensorProduct.dualDistribEquiv K M N : M^* ⊗ N^* ≃ (M ⊗ N)^*` sends
`f ⊗ g` to the functional `x ⊗ y ↦ g y * f x` (Mathlib's
`dualDistribEquiv_tmul_tmul`, which holds by `rfl`). The theorem says that this
map intertwines `(-aᵀ) ⊗ 1 + 1 ⊗ (-bᵀ)` with `-(a ⊗ 1 + 1 ⊗ b)ᵀ`. Proof: by
`TensorProduct.ext'` twice, it suffices to evaluate both sides at
`f ⊗ h` and then at `x ⊗ y`. Simplification with `map_tmul`,
`dualDistribEquiv_tmul_tmul` and `dualMap_apply` reduces both sides to
expressions in `h y`, `f (a x)`, `h (b y)` and `f x`, each equal to
`-(h y * f (a x) + h (b y) * f x)` up to rearrangement; `ring` closes the goal.

**`WeilDeligneRepresentation.tensorDualEquiv A B`.** For Weil–Deligne pairs `A`,
`B` over `K`, this is a genuine pair equivalence
`Equiv (tensor (dual A) (dual B)) (dual (tensor A B))`. Its underlying linear
equivalence is `TensorProduct.dualDistribEquiv K A B`.
- **Group action.** On the dual pairs, `g` acts by the transpose of the action
  of `g⁻¹`, and on tensors it acts factorwise. Equivariance therefore holds on
  pure tensors `f ⊗ h` evaluated at `x ⊗ y`, by `rfl`.
- **Monodromy.** The dual monodromy is `-Nᵀ` and the tensor monodromy is
  `N_A ⊗ 1 + 1 ⊗ N_B`. The monodromy condition is exactly the previous theorem
  at `a = N_A`, `b = N_B`.

The equivalence goes from the tensor of the duals to the dual of the tensor,
the same orientation and evaluation formula as in the tensor clause of the
unproved `WeilDeligneRepresentation.DualCompatibility`. This module does not
prove that proposition, whose sum and double-dual clauses are not needed here.

The additional `dualDistribEquiv_comp_map_dualMap` is the same tensor-dual
map's compatibility with tensor products of transposes. It is proved by
evaluation on pure tensors. `dualZeroMonodromyEquiv` identifies the dual of
a zero-monodromy pair with the zero-monodromy pair of the dual representation,
using the identity carrier map. `dualClass_tensorClass` descends the tensor
equivalence to isomorphism classes. The field, group and both carrier universes
remain independent. These are internal linear-algebra constructions used by
the two gamma compatibility proofs; no correspondence existence is asserted.
