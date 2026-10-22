# Rank and determinant identities for representation operations

Worker 4 authored this internal derived proof of the Library proposition
`Langlands.Weil.RepresentationRankDeterminant` in
`Langlands.Weil.Representation.Operations`. Worker 69 rechecked it and
named the exact lemmas used at each step. The closing theorem is
`Langlands.Weil.representationRankDeterminant`. Its type is the unchanged
closed target, with the same three independent universe parameters for the
group and the two carriers.

## Closing theorem

The proof introduces the group, both finite-dimensional complex carriers with
their instances, and both representations. It then supplies the five
conjuncts of the target in order.

- The three dimension formulas are Mathlib's `Module.finrank_prod`,
  `Module.finrank_tensorProduct` and `Subspace.dual_finrank_eq`.
- For each `g`, the product action is the product map of `ρ g` and `σ g`,
  so `LinearMap.det_prodMap` gives the product of the two determinants.
  The tensor clause is `det_tensorProduct_map (ρ g) (σ g)` and the
  contragredient clause is `det_representation_dual ρ g`.
- For each character `χ` and each `g`, the twist clause is
  `det_twist χ ρ g`.

## Helper lemmas

The three helpers are in the namespace `Langlands`. They work over an
arbitrary field `K`, with independent coefficient, group and vector-space
universes.

For the tensor action, `det_tensorProduct_map` chooses the finite bases
`Module.finBasis` of both vector spaces. In their tensor-product basis the
matrix of `TensorProduct.map A B` is the Kronecker product of the two
matrices, by `TensorProduct.toMatrix_map`. `Matrix.det_kronecker` gives the
two determinant powers. Their exponents are the cardinalities of the
opposite index types, which are `Fin` of the opposite dimensions.
`LinearMap.det_toMatrix` transfers this formula back to endomorphisms, and
`Fintype.card_fin` identifies the exponents with the dimensions.

The dual action at `g` is by definition the transpose (`dualMap`) of the
original action at `g⁻¹`. `LinearMap.det_dualMap` removes the transpose.
By `eq_inv_of_mul_eq_one_left` it remains to show that the determinant at
`g⁻¹` times the determinant at `g` is one. The multiplicativity of
`LinearMap.det` and of the representation, `inv_mul_cancel` and `map_one`
show this. So the dual determinant is the multiplicative inverse of the
original one.

The scalar twist action at `g` is by definition `(χ g : K)` times the
original endomorphism. `LinearMap.det_smul` therefore gives the character
value raised to the dimension, times the original determinant. This helper
does not require finite dimension: `LinearMap.det_smul` needs only a free
module, which is automatic over a field. Outside the finite-dimensional
case it inherits Mathlib's determinant and finrank conventions.

## Scope

The closing theorem specializes the helpers to the complex coefficients of
the published target and retains every rank and determinant clause. Rank
zero is included, as in the target. No topology or irreducibility is
assumed.

The proof imports the published target without changing it or its
dependencies; its only other import is
`Mathlib.LinearAlgebra.TensorProduct.Matrix`. It uses the pinned Mathlib
results described above and does not assume a project theorem or the local
Langlands correspondence. Development compilation is separate from semantic
review, formal exact-target validation and Library publication.
