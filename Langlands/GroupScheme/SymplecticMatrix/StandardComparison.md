# Comparison with the standard symplectic model

The Library has two models of the split symplectic group over a field `K`:

* `Symplectic.groupScheme K n` (module `Symplectic.Basic`): the unitary group of the standard
  alternating matrix `J` for the trivial involution, a closed subgroup of the unit group of
  `M_{2n}(K)`.
* `SymplecticMatrix.groupScheme (Fin n) K` (module `SymplecticMatrix.Basic`): the coordinate
  model corepresented by the quotient of the polynomial ring in the matrix entries by
  `g J gᵀ = J`. It is defined over every commutative ring.

In both models the points over a test scheme `T` are Mathlib's symplectic matrices
`Matrix.symplecticGroup (Fin n) Γ(T, ⊤)`. This module turns that into an isomorphism of group
schemes. It then transfers connected reductivity, and it packages the quaternionic splitting of
`Quaternionic.SymplecticReductive` as a standard model in the sense of
`Symplectic.AlgebraicModel`.

## Statements

* `Symplectic.coefficientEquiv_naturality`: the Library's scalar extension
  `coefficientEquiv K R : R ⊗[K] M_s(K) ≃ M_s(R)` commutes with coefficient changes
  `f : R → R'`.
* `Symplectic.standardPointsHom` and `standardPointsEquiv`: on points of the standard model,
  `x ↦ ambientPointsEquiv (x ≫ inclusion)` is a group isomorphism onto the symplectic matrices.
  It lands there by the Library's `mem_range_inclusion_iff`. It is injective because the
  inclusion is a closed subgroup, hence a monomorphism (`IsClosedSubgroup.mono_overHom`). It is
  surjective because every symplectic matrix lies in the range (`mem_range_inclusion_iff`
  again). `ambientPointsEquiv_naturality` and `standardPointsEquiv_naturality` give
  naturality in `T`.
* `SymplecticMatrix.comparisonIso K n : SymplecticMatrix.groupScheme (Fin n) K ≅
  Symplectic.groupScheme K n`, by the Library's `isoOfPointModels` with
  `SymplecticMatrix.pointsEquiv` on the other side.
* `Symplectic.isConnectedReductive_groupScheme`: `Symplectic.groupScheme K n` is connected
  reductive over every field `K`. This follows from `SymplecticMatrix.isConnectedReductive`
  and `IsConnectedReductive.of_iso`.
* `Quaternionic.FirstKindInvolution.nonempty_algebraicModel`: under the hypotheses of
  `isConnectedReductive_symplecticGroup`, there is a `Symplectic.AlgebraicModel` of
  `σ.symplecticGroup H` of size `card n`. The extension is the finite Galois splitting field
  `L` of `D`, which is algebraic over `K`. The isomorphism is `splittingIso` followed by
  `comparisonIso L k`. The Darboux size `k` equals `card n`: the rectangular matrices `P`, `P'`
  are mutually inverse (`card_eq_of_mul_eq_one`), so `k + k = 2 · card n`.

## Provenance

Internal module. The comparison identifies two published models with the same points. The
algebraic model packages the splitting constructed in `Quaternionic.SymplecticReductive`.
