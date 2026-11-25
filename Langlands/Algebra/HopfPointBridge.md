# Hopf points into `C ⊗ R[M]` and into `C[M]`

This module identifies two formulations of the `C`-points of the homomorphism
functor from a diagonalizable group `D(M)` to `Spec A`:

- `Langlands.FiniteBialgebraHom.IsHopfPoint R f` (module
  `Langlands.Algebra.FiniteBialgebraHom`), for
  `f : A →ₐ[R] C ⊗[R] P` with `P = R[M]` (Mathlib's bialgebra structure on
  `AddMonoidAlgebra R M`);
- `Langlands.Algebra.HopfPointExtension.IsHopfPoint g`, for
  `g : A →ₐ[R] C[M]`.

It is an internal adapter used by the chart construction for the closed torus
subgroup functor. Universes: `R`, `A`, `M` live in one
universe `u`, and `C` in another universe `v`.

## Definitions

- `scalarMap R C M : C ⊗[R] R[M] →ₐ[R] C[M]`: Mathlib's
  `AddMonoidAlgebra.scalarTensorEquiv R C`, restricted to `R`.
  `scalarMap_tmul_single` evaluates it on `c ⊗ single a r`.
- `toGroupAlgebra f := scalarMap ∘ f`.
- `squareMap R C M : C ⊗[R] (R[M] ⊗[R] R[M]) →ₐ[R] C[M × M]`, given by
  `c ⊗ (single a r ⊗ single b s) ↦ single (a, b) (c r s)` (`squareMap_tmul`).

## Results

- `squareMap_comp_map_comul`: `squareMap ∘ (id ⊗ Δ_P) = diagMap ∘ scalarMap`.
- `squareMap_comp_inclFirst`, `squareMap_comp_inclSecond`: `squareMap` turns
  the factor inclusions `inclFirst`, `inclSecond` of `FiniteBialgebraHom` into
  `inlMap` and `inrMap`.
- `groupCounit_comp_scalarMap`: the counit of `C[M]` after `scalarMap` equals
  `rid ∘ (id ⊗ ε_P)`.
- `squareMap_injective`: `squareMap` is the composite of the linear
  equivalences `C ⊗ (R[M] ⊗ R[M]) ≅ C ⊗ R[M × M]` (Mathlib's
  `AddMonoidAlgebra.tensorEquiv`) and `C ⊗ R[M × M] ≅ C[M × M]`
  (`scalarTensorEquiv`). This is checked on pure tensors of single elements.
- `isHopfPoint_iff f`: `FiniteBialgebraHom.IsHopfPoint R f ↔
  IsHopfPoint (toGroupAlgebra f)`. After `squareMap`, the two
  comultiplication composites of `FiniteBialgebraHom.IsHopfPoint` become `diagMap ∘ toGroupAlgebra f` and
  `pairMap (toGroupAlgebra f) ∘ Δ_A`. Injectivity of `squareMap` gives the
  converse. The counit conditions are identified by
  `groupCounit_comp_scalarMap`.
- `scalarMap_comp_map`, `toGroupAlgebra_pushPoint`: `toGroupAlgebra` commutes
  with change of coefficients (`pushPoint g` on the `FiniteBialgebraHom` side,
  `mapAlgHom g` on this side).
