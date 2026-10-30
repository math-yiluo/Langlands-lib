# Sections of a fibre product over products of affine opens

Author: Worker 727.

This module identifies the sections of a fibre product `P = X ×_R Y` over products of affine
opens with tensor products of sections, for single opens and for finite families, and records
how these identifications interact with restriction, with Čech differentials and with the two
axes through rational points. It is a helper for the proof of
`Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1InjectivityStatement`. It contains no
`sorry` and no new axioms.

## Setting

Everything is in namespace `Langlands.AlgebraicGeometry.Picard.FieldTwoAxisH1Injectivity`.
`R : CommRingCat.{u}` is any commutative ring (no field is needed in this module),
`πX : X ⟶ Spec R`, `πY : Y ⟶ Spec R`, and `p₁ : P ⟶ X`, `p₂ : P ⟶ Y` with
`hP : IsPullback p₁ p₂ πX πY`.

Sections are made `R`-algebras through hypotheses rather than global instances: the lemmas take
instances `[∀ W : X.Opens, Algebra R Γ(X, W)]` together with
`halgX : ∀ W, algebraMap R Γ(X, W) = (secHom πX W).hom`, where
`SmoothProperConnectedGlobalFunctionsProof.secHom πX W : R ⟶ Γ(X, W)` is the Library's map
`(Scheme.ΓSpecIso R).inv ≫ πX.appLE ⊤ W _`; likewise for `Y`. In the application the instances
are `(secHom πX W).hom.toAlgebra` and `halgX` is `rfl`.

## Definitions

- `resPi p halg U U' σ hσ : (∀ a, Γ(X, U a)) →ₗ[R] ∀ a', Γ(X, U' a')`: restriction of families
  of sections along a reindexing `σ` with `U' a' ≤ U (σ a')`, `x ↦ (x (σ a')|_{U' a'})`.
- `cechD p halg U : (∀ a, Γ(X, U a)) →ₗ[R] ∀ aa : α × α, Γ(X, U aa.1 ⊓ U aa.2)`: the first
  ordered Čech differential, `(a, a') ↦ x a' - x a` restricted to `U a ⊓ U a'`, defined as the difference
  of two `resPi`.
- `prodOpen p₁ p₂ U V := p₁ ⁻¹ᵁ U ⊓ p₂ ⁻¹ᵁ V` (abbreviation), the open `U ×_R V` of `P`.
- `tensorSec halgX halgY hP U V : CommRingCat.of (Γ(X, U) ⊗[R] Γ(Y, V)) ⟶ Γ(P, prodOpen U V)`:
  the ring map `a ⊗ b ↦ p₁^♯ a · p₂^♯ b` (`tensorSec_tmul`), built with Mathlib's
  `CommRingCat.isPushout_tensorProduct` from the commutativity `p₁ ≫ πX = p₂ ≫ πY`.
- `tensorFam halgX halgY hP U V :
  (∀ a, Γ(X, U a)) ⊗[R] (∀ b, Γ(Y, V b)) →+ ∀ a b, Γ(P, prodOpen (U a) (V b))`: the additive
  map whose `(a, b)` component is `tensorSec` after projecting both factors to `a` and `b`
  (`tensorFam_apply`, `tensorFam_tmul`).
- `evalSec halgX x₀ hx₀ W hW : Γ(X, W) →ₐ[R] R` for an `R`-point `x₀ : Spec R ⟶ X` with
  `x₀ ≫ πX = 𝟙` and `⊤ ≤ x₀ ⁻¹ᵁ W`: evaluation at `x₀`, the ring map
  `x₀.appLE W ⊤ hW ≫ (Scheme.ΓSpecIso R).hom` (`evalSec_apply`), which is `R`-linear because
  `x₀` is a section (`appLE_secHom_of_section`).

These are internal constructions. They are the standard identifications used in the proof of
the Künneth formula (Stacks, Varieties, Lemma 0BED, proof, `varieties.tex` lines 5459-5630):
`Γ(U × V, 𝒪) = Γ(U, 𝒪) ⊗ Γ(V, 𝒪)` for affine `U`, `V`, and the Čech complex of the product
cover.

## Main results

- `tensorSec_bijective halgX halgY hP hU hV`: for affine opens `U` and `V`, `tensorSec` is
  bijective. Proof: `isPushout_appLE` shows the square of section rings
  `R ⟶ Γ(X, U), Γ(Y, V) ⟶ Γ(P, prodOpen U V)` is a pushout in `CommRingCat`. It comes from
  Mathlib's `isIso_pushoutSection_of_isAffineOpen` (with `US = ⊤` of `Spec R`), translated by
  `isIso_pushoutSection_iff` and `IsPushout.of_iso'` along `Scheme.ΓSpecIso R`. Two pushouts of
  the same span are isomorphic (`IsPushout.isoIsPushout`), and the iso is `tensorSec` by the
  uniqueness of maps out of a pushout.
- `tensorFam_bijective halgX halgY hP U V hU hV` (`[Finite α] [Finite β]`, all `U a` and
  `V b` affine): `tensorFam` is bijective. Proof: it is the composite of Mathlib's linear
  equivalences `TensorProduct.piLeft` and `TensorProduct.piRight` (finite index types), which
  identify `(∏ A a) ⊗ (∏ B b)` with `∏_a ∏_b A a ⊗ B b`, followed by the product of the
  bijections `tensorSec_bijective`.
- `tensorFam_lTensor_resPi` and `tensorFam_rTensor_resPi`: `tensorFam` turns `1 ⊗ resPi` and
  `resPi ⊗ 1` into restriction of sections of `P` along the corresponding inclusions of
  products of opens. Checked on pure tensors with `Scheme.Hom.appLE_map` and
  `Scheme.Hom.map_appLE`.
- `exists_eq_smul_one_of_cechD_eq_zero p halg U hcov hglob x hx`: if `U` covers `X` and every
  global section comes from `R` (`Function.Surjective (secHom p ⊤).hom`), then every `x` with
  `cechD x = 0` is a constant `r • 1`. Proof: the components agree on overlaps, glue to a
  global section by the sheaf property (`existsUnique_gluing'`), which is `secHom p ⊤ r` for some
  `r`, and its restrictions are `r • 1` (`secHom_map`). Also `cechD_one`: `cechD 1 = 0`.
- `isAffineOpen_prodOpen hP hU hV`: `prodOpen U V` is affine for affine `U`, `V`; it is
  isomorphic to the pullback of the affine schemes `U ⟶ Spec R ⟵ V`
  (`Scheme.Hom.isPullback_resLE`).
- `iSup_prodOpen_eq_top hU hV`: if `U` covers `X` and `V` covers `Y`, the opens
  `prodOpen (U a) (V b)` cover `P` (a point `z` lies in `prodOpen (U a) (V b)` for
  `p₁ z ∈ U a`, `p₂ z ∈ V b`).
- Axis compatibility. Let `x₀ : Spec R ⟶ X` be a section of `πX` with `⊤ ≤ x₀ ⁻¹ᵁ U a₀`, and
  `i₂ : Y ⟶ P` with `i₂ ≫ p₁ = πY ≫ x₀` and `i₂ ≫ p₂ = 𝟙 Y`. Then `V b ≤ i₂ ⁻¹ᵁ prodOpen
  (U a₀) (V b)` (`le_preimage_axis₂`) and `appLE_axis₂_tensorFam`: pulling back the
  `(a₀, b)` component of `tensorFam t` along `i₂` gives the `b` component of
  `lid ((evalSec x₀ ∘ proj a₀) ⊗ 1) t`. On pure tensors `x ⊗ y` this says
  `i₂^♯(p₁^♯ (x a₀) · p₂^♯ (y b)) = (x a₀)(x₀) · y b`, using `appLE_comp_section`:
  pulling back along `πY ≫ x₀` is the scalar `evalSec x₀`. Symmetrically
  `le_preimage_axis₁` and `appLE_axis₁_tensorFam` for `y₀ : Spec R ⟶ Y` and
  `i₁ : X ⟶ P` with `i₁ ≫ p₁ = 𝟙 X`, `i₁ ≫ p₂ = πX ≫ y₀`, using `rid` and `1 ⊗ evalSec y₀`.

## Auxiliary results

- `resPi_apply`, `cechD_apply`: formulas on elements.
- `secHom_comp_fst U V`, `secHom_comp_snd U V`: `secHom πX U ≫ p₁.appLE U (prodOpen U V) _ =
  secHom (p₁ ≫ πX) (prodOpen U V)`, and the same for `p₂`.
- `ofHom_algebraMap_eq_X halgX U`, `ofHom_algebraMap_eq_Y halgY V`: the algebra maps as
  morphisms of `CommRingCat` are `secHom`.
- `id_appLE_apply W e x`: `(𝟙 Z).appLE W W e` is the identity on elements.
- `appLE_secHom_of_section halgX x₀ hx₀ W hW r`: `x₀^♯ (algebraMap R _ r)` is
  `(Scheme.ΓSpecIso R).inv r`.

## Original source

The Stacks Project at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`, registered source
`stacks-flasque-affine-vanishing-kunneth-a04446e5`: `varieties.tex`, Lemma 0BED
(`lemma-kunneth`, lines 5441-5630), whose proof uses product covers `U_i × V_j` and the
identification of sections over affine products with tensor products. The affine case
`Γ(U ×_R V, 𝒪) = Γ(U, 𝒪) ⊗_R Γ(V, 𝒪)` is taken from Mathlib
(`isIso_pushoutSection_of_isAffineOpen`).
