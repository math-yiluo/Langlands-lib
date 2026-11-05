# Dual fixed vectors of reductive groups over characteristic-zero fields

This module is internal supporting work for the characteristic-zero invariant-integral
bridge. It contains no source-cited definition.

- `algebraicClosureBaseChange ρ` is the base change of a coordinate representation
  `ρ : H ⟶ GL_{n,k}` to `K = AlgebraicClosure k`, composed with the published comparison
  `(GL_{n,k})_K ≅ GL_{n,K}`. On every test scheme `T` over `Spec K` its matrices are the
  original matrices of the corresponding point of `H` over `Spec k`
  (`algebraicClosureBaseChange_pointMatrix`). Fixed vectors stay fixed after base change.
- `contragredient_mulVec_eq_iff`: a vector is fixed by the inverse transpose of an invertible
  matrix exactly when it is fixed by the transpose.
- `exists_dual_fixed_of_algebraicClosure` (descent): if the base-changed dual representation
  fixes `c_K ∈ Kⁿ` and `c_K · v = 1` for `v ∈ kⁿ`, then the original dual representation fixes
  some `c ∈ kⁿ` with `c · v = 1`. The proof evaluates at the point of `H_K` over
  `K ⊗_k B`, where `B` is the coordinate algebra of `H`, given by the universal point in the
  second factor. There the base-changed matrix is the universal matrix `P` of `ρ` mapped into
  `K ⊗_k B`. So `Pᵀ` fixes `c_K ⊗ 1`. Applying a `k`-linear functional `φ : K → k` with
  `φ 1 = 1` to the left tensor coefficient gives a vector `c = φ ∘ c_K` fixed by `Pᵀ`.
  Hence `c` is fixed by the original dual, and `c · v = φ (c_K · v) = 1`.
- `exists_dual_fixed_of_semisimplicity`: assuming `ReductiveCharZeroSemisimplicityStatement`
  (complete reducibility over algebraically closed fields of characteristic zero), for every
  connected reductive `H` over a characteristic-zero field `k`, every coordinate
  representation and every nonzero fixed vector `v`, there is a dual fixed `c` with
  `c · v = 1`. The base change of `H` to the algebraic closure is pseudo-reductive. The
  published `exists_dual_fixed_of_rational_semisimple` supplies `c_K`, and descent finishes.
  The semisimplicity statement remains an explicit hypothesis; no Levi decomposition is used.
