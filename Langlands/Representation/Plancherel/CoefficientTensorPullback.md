# Coefficient tensors under a topological group equivalence

The coefficient tensors of a smooth representation `A` of a topological
group `G` are the algebraic tensors `A ⊗ Ǎ` of vectors with smooth
functionals (`CoefficientTensor`, module `CoefficientTensors`). Waldspurger
(2003), V.1, printed p.288 (PDF p.54), writes `E^G_P` on such tensors.
Their coefficient map `coefficientTensorMap` sends `v ⊗ ℓ` to
`g ↦ ℓ(A(g) v)`. For a continuous group isomorphism `e : H ≃ₜ* G`, the
published pullback `SmoothRep.pullback e A` is the same vector space with
the action `h ↦ A(e h)`. This module identifies its coefficient tensors
with those of `A`. The identification is internal; it uses no scheme,
orbit, measure or induction data.

## Results

- `smoothVectors_dual_comp_continuousMulEquiv`: the smooth functionals of
  `ρ ∘ e` are exactly the smooth functionals of `ρ`, as submodules of the
  algebraic dual. This repackages the published
  `isSmoothVector_dual_comp_continuousMulEquiv_iff`.
- `smoothDualPullbackEquiv e A` (definition): the resulting linear
  equivalence `Ǎ ≃ (pullback e A)ˇ`. It is the identity on algebraic
  functionals (`smoothDualPullbackEquiv_val`).
- `coefficientTensorPullbackEquiv e A` (definition): the linear
  equivalence `CoefficientTensor A ≃ CoefficientTensor (pullback e A)`.
  It is the tensor product of the identity of the common vector space with
  `smoothDualPullbackEquiv e A`. On pure tensors it keeps the vector and
  the functional (`coefficientTensorPullbackEquiv_tmul`).
- `coefficientTensorMap_coefficientTensorPullbackEquiv`: for every tensor
  `t` and `h ∈ H`,
  `coefficientTensorMap (pullback e A) (transport t) h =
  coefficientTensorMap A t (e h)`. On a pure tensor both sides are
  `ℓ(A(e h) v)`, and both sides are additive in `t`.
  `coe_coefficientTensorMap_coefficientTensorPullbackEquiv` states the same
  identity as functions, `… = coefficientTensorMap A t ∘ e`.
- `coefficientTensorAction_coefficientTensorPullbackEquiv`: the external
  action of `(h₁, h₂) ∈ H × H` on a transported tensor equals the transport
  of the action of `(e h₁, e h₂)`. On pure tensors this is the equality of
  the contragredient actions, from the published `dual_comp_monoidHom`.

## Intended use

Worker 301's staged `FullLeviInduction` defines
`fullLeviAmbientSmoothRep M hM A` as
`SmoothRep.of (A.representation.comp (fullLeviGroupEquiv M hM).toMonoidHom) _`.
This is definitionally `SmoothRep.pullback (fullLeviGroupEquiv M hM) A`, so
the results above apply to it with `e = fullLeviGroupEquiv M hM`. This
module does not compare product-induced coefficient tensors with the
ambient ones.
