# Level groupoids of multiplicative coactions

Author: Worker 266.

## Setting

`t₀ : B₀ →+* C₀` is a ring étale groupoid (`RingEtaleGroupoid`, module
`RingEtaleGroupoid`), with source algebra structure `B₀ → C₀`. `D` is a
`B₀`-algebra with a Library coaction `θ : GroupoidCoaction t₀ D` (module
`EtaleEquivalenceRelationComodule`). Geometrically `θ` is an action of the
groupoid `Spec C₀ ⇉ Spec B₀` on `Spec D` over `Spec B₀`. The level groupoid
`Spec (C₀ ⊗[B₀] D) ⇉ Spec D` is its action groupoid. A point of
`C₀ ⊗[B₀] D` is a pair `(r, y)` with `s₀ r` equal to the image of `y`; the
source is `y` and the target is `r · y`. In the proof of NL, `D` is a finitely
generated stable subalgebra of `Γ(E.U)`, and this groupoid is the level relation
`E_D` of step 2 of the task's `context.md`. The relation ring is `C₀ ⊗[B₀] D`,
the source map is `d ↦ 1 ⊗ d` (`Algebra.TensorProduct.rightAlgebra`, a local
instance), and the target map is `θ` itself.

## Declarations

Ring maps out of tensor products:

* `RingEtaleGroupoid.tensor_ringHom_ext`: ring maps out of `C₀ ⊗[B₀] D` agree
  if they agree on `c ⊗ 1` and `1 ⊗ d`.
* `RingEtaleGroupoid.tensorLift φ ρ h`: the ring map `c ⊗ d ↦ φ c * ρ d`, for
  ring maps `φ`, `ρ` that agree on `B₀`. `tensorLift_tmul` is its formula.
* `RingEtaleGroupoid.algebraMap_tmul_one`: `b ⊗ 1 = 1 ⊗ b` for `b ∈ B₀`.

Evaluating the coaction identities. For a `B₀`-algebra `T`,
`RingEtaleGroupoid.evalMap ρ : T ⊗[B₀] D → T` is `x ⊗ d ↦ x * ρ d`.
`evalMap_tmul`, `evalMap_smul` and `evalMap_rTensor` are its formulas;
`evalMap_rTensor` identifies `evalMap ρ ∘ (φ ⊗ id)` with the product map of `φ`
and `ρ`. Applying `evalMap` to the Library axioms `counit` and `coassoc` of
`GroupoidCoaction` gives `productMap_coaction_of_counit` and
`evalMap_coactionCompose`. These lemmas turn the axioms into identities of ring
maps out of `C₀ ⊗[B₀] D`.

Multiplicative coactions. `GroupoidCoaction.IsMultiplicative θ` says that
`θ.coaction` preserves `1` and products. `GroupoidCoaction.toRingHom` is `θ` as a
ring map (`toRingHom_apply`). `coaction_algebraMap` gives
`θ (b • 1) = t₀ b ⊗ 1`.

The level groupoid. `RingEtaleGroupoid.level hE₀ θ hθ` is the statement
`RingEtaleGroupoid (θ.toRingHom hθ)` for the relation ring `C₀ ⊗[B₀] D`. Its
fields are proved separately:

* `level_hom_ext`: two maps out of `C₀ ⊗[B₀] D` that agree after the source and
  the target map agree on `C₀`. On `t₀(B₀)` this holds through the target map,
  because `θ (b • 1) = t₀ b ⊗ 1`. On the source image of `B₀` it holds through
  `1 ⊗ D`. The field `hom_ext` of `hE₀` then applies, and
  `tensor_ringHom_ext` concludes.
* `level_refl`: at a point `a : D → T` the identity point is the product of
  `a` with `hE₀.identity` (whose target law is `identity_point`). The counit
  identity shows that its target is `a`.
* `level_symm`: for a point `φ` with source `a = φ(1 ⊗ –)` and target
  `b = φ ∘ θ`, take the inverse `ψ₀` of its `C₀`-component `φ(– ⊗ 1)` (field
  `symm` of `hE₀`) and the ring map `tensorLift ψ₀ b`. Its source is `b`. Its
  target is `a` by the cocycle identity for the composable pair `(ψ₀, φ(– ⊗ 1))`
  with composite an identity point, evaluated with `evalMap`.
* `level_trans`: for composable `φ`, `ψ`, compose their `C₀`-components with
  the field `trans` of `hE₀` to get `κ`, and take `tensorLift κ (ψ(1 ⊗ –))`.
  The cocycle identity for `(φ(– ⊗ 1), ψ(– ⊗ 1))` with composite `κ` gives its
  target.
* `level_etale_algebraMap`: `d ↦ 1 ⊗ d` is étale, by Mathlib's
  `RingHom.Etale.isStableUnderBaseChange` and the pushout instance
  `TensorProduct.isPushout`.
* `etale_of_symm`: for any ring groupoid, the target map is étale once the
  source map is. The symmetry point `σ` with `σ ∘ t = s` and `σ ∘ s = t` is an
  involution by `hom_ext`, so `t = σ ∘ s` with `σ` bijective.

Conversely, `RingEtaleGroupoid.coactionOfLevel hE₀ τ hτ hG` turns a ring
étale groupoid `τ : D →+* C₀ ⊗[B₀] D` with source `d ↦ 1 ⊗ d` and
`τ (b • 1) = t₀ b ⊗ 1` into a `GroupoidCoaction t₀ D` with coaction `τ`
(`coactionOfLevel_coaction`), which is multiplicative
(`coactionOfLevel_isMultiplicative`). The counit identity at `φ : C₀ → T` is
obtained by comparing `φ ⊗ id` with the reflexivity point of `τ` at
`d ↦ 1 ⊗ d`; the cocycle identity, by comparing `φ₃ ⊗ id` with the transitivity
point of a composable pair built from `φ₁` and `φ₂ ⊗ id`. In both comparisons
the two maps agree on `C₀` by the field `hom_ext` of `hE₀` and on `D` by
construction. `rTensor_eq_map` and `smul_eq_tmul_one_mul` are the tensor
identities used.

Other declarations:

* `RingEtaleGroupoid.ofRingEquiv`: a ring étale groupoid can be transported
  along a ring isomorphism of relation rings that is compatible with the source
  algebra structures. Étaleness is transported by `RingHom.Etale.respectsIso`.
* `RingEtaleGroupoid.isCartesianHom_of_equivariant hG hG' φ hφ`: let
  `φ : D →ₐ[B₀] D'` be equivariant, `(C₀ ⊗ φ) ∘ τ = τ' ∘ φ`. Then
  `(Spec φ, Spec (C₀ ⊗ φ))` is a cartesian morphism (Library
  `EtaleEquivalenceRelation.IsCartesianHom`) from `hG'.toScheme` to
  `hG.toScheme`. Commutation with the targets is the equivariance. The pullback
  square is the image under `Spec` (`isPullback_SpecMap_of_isPushout`) of the
  pushout square `D → C₀ ⊗ D`, `D → D'`, `C₀ ⊗ D → C₀ ⊗ D'`. That square is a
  pushout by `IsPushout.of_top` applied to the tensor-product pushouts
  `CommRingCat.isPushout_tensorProduct` for `D` and `D'`.

## Provenance and scope

The level relation is step 2 of the ring-level route in the task's `context.md`
for the proof of Stacks Project Lemma 70.15.1 (Tag 07VS). Stacks Project
Definition 39.14.1 (Tag 03LI) defines modules on groupoids; the Library's
`GroupoidCoaction` encodes them. The proofs here are internal and follow the
outline above. The module states nothing about stability, finite generation or
Noetherian rings.
