# The induced σ-intertwiner of a normalized product induction

Let `E/F` be an extension of nonarchimedean local fields with an `F`-algebra
automorphism `σ` of `E`. Fix a block shape `B` of `n` with blocks of sizes
`n₁, …, n_r`. Let `P₁, …, P_r` be complex representations of the blocks
`GL_{nᵢ}(E)` with σ-intertwiners `Aᵢ`. This module constructs Henniart–Lemaire's
induced operator

```text
ι(A)(ξ)(g) = (A₁ ⊗ ⋯ ⊗ A_r)(ξ(g^{σ⁻¹}))
```

on the normalized product induction `i(P₁, …, P_r)` and proves that it is a
σ-intertwiner, as Henniart–Lemaire II.4.4 asserts. It also proves the
admissibility of normalized product inductions of admissible families.

Two declarations form the definition: `Langlands.Induction.transportSmoothEquiv`
(generic) and `Langlands.BaseChange.inducedSigmaIntertwiner` (the operator
`ι(A)`). The other declarations are the lemmas they need. The module proves no
σ-lift and no character identity. It is the first step towards
`Langlands.BaseChange.SigmaLiftInductionStatement`, whose conclusion needs
admissibility proofs for both normalized product inductions and a σ-intertwiner
of the induction over `E`.

## Source

Henniart–Lemaire, *Changement de base et induction automorphe pour `GL_n` en
caractéristique non nulle*, Mém. SMF 124 (2011), cited as HL. The PDF page is
the printed page plus 8.

- HL II.4.4, printed p. 85 (PDF p. 93), first paragraph after the reduction
  to the case where `E` is a field. Let `α = (α₁, …, α_m)` be a block shape
  and `Πᵢ` smooth σ-stable representations of `GL_{αᵢ}(E)` with isomorphisms
  `Aᵢ : Πᵢ ≅ Πᵢ^σ`. HL write `Ξ = Π₁ ⊗ ⋯ ⊗ Π_m` and `B = A₁ ⊗ ⋯ ⊗ A_m`
  (their `B` is not a block shape). Then the induced representation
  `ι_α(Ξ) = Π₁ × ⋯ × Π_m` is σ-stable, and the operator `ι_α(B)` given by
  `ι_α(B)(ξ)(g) = B(ξ(g^{σ⁻¹}))` is an isomorphism of `ι_α(Ξ)` onto
  `ι_α(Ξ)^σ`.

HL state this without proof. The verification here is the
expected one, with the inputs made explicit:

1. `g ↦ g^σ` is a topological automorphism of `GL_n(E)` that maps the standard
   parabolic subgroup to itself. Its restriction to the parabolic commutes with
   the projection to the Levi subgroup.
2. The tensor product of the `Aᵢ` intertwines the Levi representation
   `P₁ ⊗ ⋯ ⊗ P_r` with its pullback along `σ`.
3. The half modulus `δ_P^{1/2}` is σ-invariant, because the normalized absolute
   value of `E` is.

The generic transport isomorphism, the continuity lemmas and the σ-invariance
of the normalized absolute value are internal lemmas. They are not stated in
HL.

## Library conventions

- `entrywiseAut σ n : GeneralLinear n E ≃* GeneralLinear n E` is `g ↦ g^σ`.
  `leviAut σ B` is its blockwise action on the Levi product.
  `entrywiseAut_mem_parabolic_iff` and `leviProjection_entrywiseAut` are in
  `Langlands.BaseChange.PseudoCoefficient`.
- `SigmaIntertwiner σ n τ` is `Representation.Equiv τ (τ.comp (entrywiseAut σ n))`.
  Its linear equivalence `A` satisfies `A ∘ τ(g) = τ(g^σ) ∘ A`.
- `(LocalFieldData.ofInstances E).normalizedProductInduced B P` is
  `normalizedParabolicInduced B (B.blockTensor P)`. Its space is the space of
  smooth functions `ξ : GL_n(E) → ⊗ᵢ Wᵢ` with
  `ξ(p g) = δ_P^{1/2}(p) (⊗ᵢ Pᵢ)(m(p)) ξ(g)`. Here `m(p)` is the Levi
  projection. The group acts by right translation.

## Contents

### Generic transport (`namespace Langlands.Induction`)

Let `G` be a topological group, `P` a subgroup, and `ρ`, `τ` representations
of `P`.

- `exists_openSubgroup_eval_mul`: a smooth induced function is invariant under
  right translation by some open subgroup. It unfolds the smoothness field of
  `SmoothFunctions`.
- `transportSmoothFunction P θ hθ θP hθP T hT f`: the smooth induced function
  `x ↦ T(f(θ⁻¹ x))`. Here `θ` is an automorphism of `G` with continuous
  inverse, and `θP` is an automorphism of `P` that agrees with `θ` on `P`.
  The linear map `T` satisfies `T ∘ ρ(p) = τ(θP p) ∘ T`. Covariance follows
  from `θ⁻¹(p x) = θP⁻¹(p) θ⁻¹(x)` and the hypothesis on `T`. Smoothness uses
  the preimage under `θ⁻¹` of the open subgroup fixing `f`.
  `eval_transportSmoothFunction` records the formula (`rfl`).
- The private lemma `smoothTransport_ext` identifies two smooth induced
  functions when their values agree.
- `transportSmoothLinearMap`: `transportSmoothFunction` as a linear map.
- `transportSmoothEquiv P θ hθ hθ' θP hθP T hT`: for a homeomorphic automorphism `θ`
  and a linear equivalence `T` as above, an isomorphism of representations

  ```text
  smoothInduced P ρ ≅ (smoothInduced P τ) ∘ θ.
  ```

  Its inverse is the transport along `θ⁻¹`, `θP⁻¹` and `T⁻¹`. The
  intertwining identity is `θ⁻¹(x) g = θ⁻¹(x θ(g))`. `eval_transportSmoothEquiv`
  records `transportSmoothEquiv … f x = T(f(θ⁻¹ x))` (`rfl`).

### The entrywise action and the absolute value (`namespace Langlands.BaseChange`)

- `continuous_algEquiv`: an `F`-algebra automorphism of `E` is continuous when
  `E` carries the `F`-module topology (`IsModuleTopology F E`). It is
  `F`-linear, and Mathlib's `IsModuleTopology.continuous_of_linearMap`
  applies.
- `continuous_entrywiseAut`, `continuous_entrywiseAut_symm`: `g ↦ g^σ` and its
  inverse `g ↦ g^{σ⁻¹}` are continuous on `GL_n(E)`. They are `Units.map` of
  the entrywise matrix map (`Continuous.units_map`, `Continuous.matrix_map`).
- `normalizedAbsUnits_map_ringEquiv`: on a nonarchimedean local field `E`, the
  normalized absolute value `|·|_E` of `LocalFieldData.ofInstances E` is
  invariant under every ring automorphism `τ` with `τ` and `τ⁻¹` continuous.

  *Proof.* Let `μ` be an additive Haar measure on `E` and `ν = τ_* μ`. Then
  `ν` is again an additive Haar measure (Mathlib's
  `AddEquiv.isAddHaarMeasure_map`). By
  `Langlands.AllField.HarmonicAnalysis.padicScalarHaarScaling`, multiplication
  by `b` pushes any additive Haar measure forward to `|b|_E⁻¹` times itself.
  Since `τ(a x) = τ(a) τ(x)`, the push-forward of `ν` along multiplication by
  `τ(a)` equals the push-forward along `τ` of the push-forward of `μ` along
  multiplication by `a`. Hence `|τ(a)|_E⁻¹ • ν = |a|_E⁻¹ • ν`. Evaluating both
  sides on a compact neighbourhood of `0`, which has finite positive
  `ν`-measure, gives `|τ(a)|_E = |a|_E`. The proof installs the Borel
  σ-algebra and the topology of `LocalFieldData.ofInstances E` as local
  instances.
- `normalizedAbsUnits_algEquiv`: the special case `τ = σ`, using
  `continuous_algEquiv` for `σ` and `σ⁻¹`.
- `determinantNorm_entrywiseAut`: `|det g^σ|_E = |det g|_E`, because
  `det(g^σ) = σ(det g)` (`Matrix.GeneralLinearGroup.map_det`).
- `leviModulus_leviAut`: the modulus of the standard block Levi is σ-invariant.
  The Library's `leviModulus_apply` writes it as a product of powers of the
  block determinant norms, and each factor is σ-invariant.

### The parabolic subgroup

- `parabolicAut σ B`: the restriction of `g ↦ g^σ` to the standard parabolic
  subgroup of `B`, as a group automorphism. Its inverse uses `σ⁻¹`.
  `coe_parabolicAut` records that it agrees with `entrywiseAut σ n` (`rfl`).
- `leviProjection_parabolicAut`: `m(p^σ) = leviAut σ B (m(p))`
  (`leviProjection_entrywiseAut`).
- `parabolicHalfModulus_parabolicAut`: `δ_P^{1/2}(p^σ) = δ_P^{1/2}(p)`, from
  `parabolicHalfModulus_apply`, `leviHalfModulus_apply` and
  `leviModulus_leviAut`.

### The tensor product of the block intertwiners

- `leviTensorIntertwiner σ B A`: the tensor product `A₁ ⊗ ⋯ ⊗ A_r`
  (`PiTensorProduct.congr`) is an isomorphism of `B.blockTensor P` with its
  pullback along `leviAut σ B`. The intertwining identity is checked on pure
  tensors (`PiTensorProduct.ext`, `blockTensor_tprod`, `congr_tprod`), where it
  is the identity of each `Aᵢ`.
- `leviTensorIntertwiner_tprod`: its value on a pure tensor (`congr_tprod`).
- `isLeviSigmaStable_blockTensor`: hence `B.blockTensor P` is σ-stable as a
  representation of the Levi product (`IsLeviSigmaStable`).

### The induced intertwiner

- `leviTensorIntertwiner_inducing`: `A₁ ⊗ ⋯ ⊗ A_r` intertwines the inducing
  representation `p ↦ δ_P^{1/2}(p) (⊗ᵢ Pᵢ)(m(p))` of the parabolic with its
  pullback along `parabolicAut σ B`. It combines
  `parabolicHalfModulus_parabolicAut`, `leviProjection_parabolicAut` and the
  intertwining identity of `leviTensorIntertwiner`.
- `inducedSigmaIntertwiner σ B A : SigmaIntertwiner σ n
  ((LocalFieldData.ofInstances E).normalizedProductInduced B P)`: HL's
  operator `ι(A)`. It is `Induction.transportSmoothEquiv` with `θ = entrywiseAut σ n`,
  `θP = parabolicAut σ B`, `ρ = τ` the inducing representation, and
  `T = leviTensorIntertwiner σ B A`. The normalized product induction unfolds
  definitionally to the smooth induction of the inducing representation.
- `eval_inducedSigmaIntertwiner`: the defining formula
  `ι(A)(ξ)(g) = (A₁ ⊗ ⋯ ⊗ A_r)(ξ(g^{σ⁻¹}))` (`rfl`).
- `isSigmaStable_normalizedProductInduced`: the normalized product induction of
  a family of σ-stable representations is σ-stable.

### Admissibility

- `isAdmissible_normalizedProductInduced`: over a nonarchimedean local field
  `F`, if every `πᵢ` is admissible, then so is the normalized product induction
  `(LocalFieldData.ofInstances F).normalizedProductInduced B π`. The proof
  applies `Langlands.AllField.Parabolic.normalizedInductionAdmissibility` to
  `B.blockTensor π`. The latter is admissible by
  `FiniteTensor.isAdmissible_external`. This is the classical admissibility of
  parabolic induction for `GL_n` (Bernstein–Zelevinsky). It supplies the
  admissibility proofs that the conclusion of
  `Langlands.BaseChange.SigmaLiftInductionStatement` requires, over `F` and over
  `E`.

## Scope

The module defines no σ-lift and proves no character identity. It does not use
cyclicity of `σ` or irreducibility. The intertwiner is defined for arbitrary
complex representations of the blocks. Admissibility is proved for arbitrary
admissible families.
