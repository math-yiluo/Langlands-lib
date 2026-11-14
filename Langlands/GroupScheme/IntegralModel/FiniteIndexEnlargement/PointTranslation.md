# Translation of coordinates by integral points of a bialgebra

Worker 33, task `e1575004-9fac-4821-9bc9-ddcb15e7cbf3` (Task 6018). This is an internal helper
module for the proof of
`Langlands.GroupScheme.IntegralModel.FiniteIndexEnlargementStatement`. Its definitions
(`pointTrans`, `transEquiv`) are standard Hopf-algebra constructions, derived here for this
proof.

## Content

Let `C` be a commutative bialgebra over a commutative ring `R`.

- `pointTrans f : C →ₐ[R] C`, for an `R`-point `f : C →ₐ[R] R`, is right translation by `f`:
  `c ↦ ∑ f (c₂) c₁`, where `Δ c = ∑ c₁ ⊗ c₂`. Formally it is `rid ∘ (id ⊗ f) ∘ Δ` as an
  algebra map. `pointTrans_apply` and `pointTrans_toLinearMap` give the linear-map form, using
  `algebraRid_apply` to compare the algebra and linear versions of `rid`.
- `pointTrans_one`: translation by the unit of the convolution monoid (the counit) is the
  identity, by the counit axiom `Coalgebra.lTensor_counit_comul`.
- `comp_pointTrans`: for any `R`-algebra `S` and `y : C →ₐ[R] S`, `y ∘ pointTrans f` is the
  convolution product `y * (ofId ∘ f)`. Check on pure tensors of `Δ c`.
- `pointTrans_pointTrans_apply` and `pointTrans_comp`:
  `pointTrans f ∘ pointTrans g = pointTrans (f * g)` (convolution product). The proof
  rewrites both sides as maps on `(C ⊗ C) ⊗ C` and applies coassociativity
  (`Coalgebra.coassoc_apply`).
- `map_pointTrans`: translations are natural along a bialgebra map `φ : C →ₐc[R] D`:
  `φ (pointTrans (f ∘ φ) c) = pointTrans f (φ c)`. This uses that `φ` commutes with
  comultiplication.
- `transEquiv σ z : C ≃ₐ[R] C`, for a group `Γ` and a monoid homomorphism
  `σ : Γ →* WithConv (C →ₐ[R] R)`, is the algebra automorphism `pointTrans (σ z)`. Its inverse
  is `pointTrans (σ z⁻¹)`, by `pointTrans_comp` and `pointTrans_one`. `transEquiv_apply` is its
  defining equation.

No external statement is asserted.
