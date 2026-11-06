# Chart derivatives of the group law and of conjugation

Module `Langlands.Global.LocalModularCharacter.ChartLie`.

This module links the analytic chart of `G(K)` at the identity with the algebraic Lie kernel
`lieKernel G K`. That kernel is the set of dual-number points of `G` that reduce to the identity,
and the Library's adjoint action `adjoint G K` acts on it. The result is the input to the
modular-character estimates. The derivative of the chart expression of conjugation by `g` is a
linear automorphism of `K^d` with the same determinant as `adjoint G K g`.

Throughout, `F` is a field, `G` an affine group scheme over `Spec F`, and `K` a nontrivially normed
field that is an `F`-algebra. For the chart section, `G(K) = Lie.AffinePoints G K` carries an
arbitrary topology with continuous multiplication. At the places of a number field this is the
Library's regular-function topology.

This is internal infrastructure for the task. No literature statement is formalized here. The
idea is the standard "tangent vectors are dual-number points" picture, applied to families of
points whose coordinates are strictly differentiable. Its realization is internal to this
development. The proofs work with the functor of points only and use no Hopf-algebra formulas.

## Jets (section `Jet`)

- `differentiableAt_of_mem_strictDiffSubalgebra`: elements of `strictDiffSubalgebra F K t₀` (from
  `RegularFamily`) are differentiable at `t₀`.
- `jet F t₀ v : strictDiffSubalgebra F K t₀ →ₐ[F] DualNumber K` sends `h` to
  `h t₀ + ε · (fderiv K h t₀ v)`. The product rule for `fderiv` makes it an algebra map.
  `jet_fst` and `jet_snd` compute its components.

## Tangent vectors of regular families (section `Tangent`)

For a regular family `f : T → G(K)` at `t₀`, `familyTangent G t₀ v f hf` is the dual-number point
`Lie.affineMap G (jet F t₀ v) (liftFamily G _ f hf)`.

- `affinePointEvaluation_familyTangent`: its value on a global section `a` is
  `inl (a(f t₀)) + inr (fderiv K (t ↦ a(f t)) t₀ v)`.
- `affinePointEvaluation_constant` and `affinePointEvaluation_reduction` compute evaluations of
  `Lie.constant` and `Lie.reduction`, using naturality of evaluation.
- `reduction_familyTangent`: the tangent vector reduces to `f t₀`.
- `familyTangent_mul`: the tangent of a pointwise product is the product of the tangents. This
  follows from `liftFamily_mul` and multiplicativity of `Lie.affineMap`.
- `familyTangent_const`: the tangent of a constant family `g` is `Lie.constant G g`.
- `familyTangent_congr`: families that agree near `t₀` have equal tangents.
- `IsRegularFamily.comp_hasStrictFDerivAt` and `familyTangent_comp`: precomposition with a
  strictly differentiable map `σ` with `σ t₁ = t₀` preserves regularity. The tangent in direction
  `v` equals the tangent of `f` in direction `σ' v` (chain rule).

Equalities of points are proved through `affinePointEvaluation_injective`: a point of the affine
scheme is determined by its values on global sections.

## Kernel coordinates (section `Coordinates`, assuming `[IsAffineHom G.X.hom]`)

- `coordinateComparison : AffineCoordinateRing F G.X →ₐ[F] Lie.coordinateAlgebra G` is defined by
  the universal point of `Lie.coordinateAlgebra G`.
- `affinePointEvaluation_eq_pointCoordinates`: evaluating a global section `a` at a point `y` is
  `Lie.pointCoordinates G y (coordinateComparison G a)`. The proof writes `y` as the image of the
  universal point.
- `kernelCoordinateMap G c : Additive (lieKernel G K) →ₗ[K] (Fin n → K)` takes the coordinates
  `Lie.kernelDerivationEquiv G y (coordinateComparison G (c j))`. It is linear by
  `Lie.kernelDerivationEquiv_mul` and `Lie.kernelDerivationEquiv_scale`. `kernelCoordinateMap_apply`
  identifies them with the `ε`-parts of the values of `y` on the global sections `c j`.
- `injective_kernelCoordinateMap`: assume that every `F`-linear derivation
  `D : AffineCoordinateRing F G.X →ₗ[F] K` at the identity point with `R' (D ∘ c) = 0` is zero.
  Then `R' ∘ₗ kernelCoordinateMap G c` is injective. The `ε`-part of a kernel point is such a
  derivation, and a kernel point with zero `ε`-part is the identity.

## The chart theorem (section `Chart`)

Data: a chart `φ : OpenPartialHomeomorph (G(K)) (Fin d → K)`, global sections
`c : Fin n → AffineCoordinateRing F G.X`, and `R : (Fin n → K) → (Fin d → K)` with strict
derivative `R'` at the coordinates of the identity. Near the identity, `φ x = R (c(x))`.

- `hasStrictFDerivAt_chart_comp`: if `f` is a regular family with `f t₀ = 1` and `f t ∈ φ.source`
  near `t₀`, then `t ↦ φ (f t)` is strictly differentiable at `t₀`. Its derivative is
  `R' ∘ (t ↦ (c_j(f t))_j)'`, by the chain rule.
- `chart_derivatives`: the hypotheses are `1 ∈ φ.source` and `φ 1 = 0`, the two conditions on
  `R` above, `hreg` (every global section of `φ.symm` is strictly differentiable at `0`), and
  `hinj` (the derivation condition of `injective_kernelCoordinateMap`). The conclusions are the
  following.
  1. The chart expression of the group law, `(s, t) ↦ φ(φ⁻¹ s · φ⁻¹ t)`, is strictly
     differentiable at `0` with a derivative `L` satisfying `L (0, w) = w`.
  2. For every `g`, `z ↦ φ(g · φ⁻¹ z · g⁻¹)` is strictly differentiable at `0` with derivative a
     continuous linear automorphism `A` of `K^d`. Moreover `det A = det (adjoint G K g)`.

Proof of `chart_derivatives`. By `hreg`, `φ.symm` is a regular family at `0`. Products and
constants of regular families are regular, so the families `(s,t) ↦ φ⁻¹ s · φ⁻¹ t` and
`z ↦ g φ⁻¹(z) g⁻¹` are regular as well. `hasStrictFDerivAt_chart_comp` then gives the strict
derivatives. `L (0, w) = w` holds because `φ(φ⁻¹ 0 · φ⁻¹ w) = w` near `0`, by uniqueness of
derivatives.

For conjugation, let `tg v := familyTangent G 0 v φ.symm`, a point of the Lie kernel because it
reduces to `φ⁻¹ 0 = 1`. Let `κ := R' ∘ kernelCoordinateMap G c`. Since `φ ∘ φ⁻¹ = id` near `0`,
the derivative computation gives `κ (tg v) = v`. `κ` is injective by `injective_kernelCoordinateMap`,
so `κ` is a linear equivalence with inverse `tg`. Let `A'` be the derivative of the conjugation
chart expression `ψ`. Then `Ad(g)(tg v) = tg (A' v)`: by `adjoint_val`, `familyTangent_const` and
`familyTangent_mul`, the left side is the tangent of `z ↦ g φ⁻¹(z) g⁻¹`. That family equals
`φ⁻¹ ∘ ψ` near `0`, and `familyTangent_comp` turns its tangent in direction `v` into the tangent of
`φ⁻¹` in direction `A' v`. Hence `A' = κ ∘ Ad(g) ∘ κ⁻¹`, and `LinearMap.det_conj` gives the
determinant identity. Continuity of the linear maps on `K^d` comes from
`LinearMap.continuous_on_pi`.
