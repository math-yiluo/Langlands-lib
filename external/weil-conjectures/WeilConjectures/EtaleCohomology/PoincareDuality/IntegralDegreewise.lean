/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.CategoryTheory.DerivedCategory.Complete.QuotPowTriangle
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Linear
public import WeilConjectures.CategoryTheory.DerivedCategory.UniversalCoefficient
public import WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise
public import WeilConjectures.Mathlib.CategoryTheory.Sites.GlobalSections
public import WeilConjectures.SixFunctors.Etale.Derived.ReductionConservative

/-!
# The integral degreewise form of Poincaré duality

Let `Λ` be a commutative ring and `ϖ ∈ Λ` a nonzerodivisor, the intended case being the
integral stage `Λ = 𝒪_E` with a uniformizer `ϖ`, so that `A_{E,n} = Λ ⧸ (ϖ)ⁿ`. For
`K ∈ D(X_ét, Λ)` write `K_n = K ⊗ᴸ (Λ ⧸ (ϖ)ⁿ)_X` (`AlgebraicGeometry.Etale.reductionModIdeal`).
This file proves blueprint `prop-pod-integral-degreewise-form`:

* the universal coefficient sequences
  `0 ⟶ Hⁱ_c(X, K) ⊗ A_{E,n} ⟶ Hⁱ_c(X, K_n) ⟶ Tor₁(Hⁱ⁺¹_c(X, K), A_{E,n}) ⟶ 0`
  are short exact, and so are the corresponding sequences for the ordinary cohomology
  `Hʲ(X, L)` of the second variable `L = K^∨(d)` of the Poincaré pairing;
* when the cohomology modules are finite projective, the Tor terms vanish, and the derived
  Poincaré duality at the integral stage gives `H^{2d-i}(X, K^∨(d)) ≅ Hⁱ_c(X, K)^∨`.

## Main definitions

- `AlgebraicGeometry.Etale.reductionSequence`: for a triangulated `Λ`-linear functor
  `Φ : D(X_ét, Λ) ⥤ D(Λ)`, the short complex
  `Hⁱ(Φ K) ⊗ A_n ⟶ Hⁱ(Φ K_n) ⟶ Tor₁(Hⁱ⁺¹(Φ K), A_n)`.
- `AlgebraicGeometry.Etale.compactlySupportedReductionSequence`,
  `AlgebraicGeometry.Etale.cohomologyReductionSequence`: the cases `Φ = RΓ_c(X/Y, -)` and
  `Φ = RΓ(X, -)`.

## Main statements

- `AlgebraicGeometry.Etale.shortExact_compactlySupportedReductionSequence`,
  `AlgebraicGeometry.Etale.shortExact_cohomologyReductionSequence`: the universal coefficient
  sequences are short exact.
- `AlgebraicGeometry.Etale.isIso_compactlySupportedReductionSequence_f`,
  `AlgebraicGeometry.Etale.isIso_cohomologyReductionSequence_f`: for flat cohomology the Tor
  terms vanish and `Hⁱ(X, K) ⊗ A_n ≅ Hⁱ(X, K_n)`.
- `AlgebraicGeometry.Etale.integralDegreewiseDuality`: at a separably closed point, if the
  compactly supported cohomology modules are finite projective, then so are the
  `H^{2d-i}(X, K^∨(d))`, and `H^{2d-i}(X, K^∨(d)) ≅ Hom_Λ(Hⁱ_c(X, K), Λ)`.

## Implementation notes

The universal coefficient sequences come from the distinguished triangle
`K ⟶[ϖⁿ] K ⟶ K_n ⟶ K⟦1⟧` (`K` tensored with `Λ ⟶[ϖⁿ] Λ ⟶ Λ/(ϖ)ⁿ`), carried to `D(Λ)` by the
triangulated `Λ`-linear functor `RΓ_c` or `RΓ`, together with the long exact cohomology
sequence (`DerivedCategory.universalCoefficientSequence_shortExact`). They hold for every
`K`; the blueprint assumes `K` perfect, which is only used for the duality statement.

As in `WeilConjectures.EtaleCohomology.PoincareDuality.Degreewise`, the degreewise duality is
proved in the non-canonical form of an abstract isomorphism of `Λ`-modules: the comparison of
the degreewise pairing with the cohomology of `RΓ(Spec k, -)` needs the lax monoidal structure
of `RΓ(Spec k, -)`, which the repository does not have.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite Pretriangulated

open scoped CategoryTheory.Functor TensorProduct

namespace AlgebraicGeometry

open Scheme

namespace Etale

section Instances

variable {Λ : Type (u + 1)} [CommRing Λ]

/-- The derived global sections `RΓ(Y, -)` are `Λ`-linear. -/
instance linear_rightDerivedGlobalSections (Y : Scheme.{u}) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).Linear Λ :=
  inferInstanceAs
    ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.Linear Λ)

/-- The derived global sections `RΓ(Y, -)` are triangulated. -/
instance isTriangulated_rightDerivedGlobalSections (Y : Scheme.{u}) :
    (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) Y).IsTriangulated :=
  inferInstanceAs
    ((Sheaf.Γ Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)).rightDerivedFunctor.IsTriangulated)

variable {X Y : Scheme.{u}} (a : X ⟶ Y) [HasCompactification a]

/-- The compactly supported derived global sections commute with shifts. -/
noncomputable instance commShift_compactlySupportedGlobalSections :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).CommShift ℤ :=
  inferInstanceAs ((R(a)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections _ Y).CommShift ℤ)

/-- The compactly supported derived global sections are `Λ`-linear. -/
instance linear_compactlySupportedGlobalSections :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).Linear Λ :=
  inferInstanceAs ((R(a)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections _ Y).Linear Λ)

/-- The compactly supported derived global sections are triangulated. -/
instance isTriangulated_compactlySupportedGlobalSections :
    (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).IsTriangulated :=
  inferInstanceAs
    ((R(a)_![ModuleCat.{u + 1} Λ] ⋙ rightDerivedGlobalSections _ Y).IsTriangulated)

end Instances

section Reduction

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ}
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ)
  (Φ : DerivedCategoryModule Λ X ⥤ _root_.DerivedCategory (ModuleCat.{u + 1} Λ))
  [Φ.CommShift ℤ] [Φ.IsTriangulated] [Φ.Linear Λ] (K : DerivedCategoryModule Λ X)

/-- The image under `Φ` of the triangle `K ⊗ᴸ (Λ ⟶[ϖⁿ] Λ ⟶ Λ/(ϖ)ⁿ ⟶ Λ⟦1⟧)`. -/
noncomputable abbrev reductionTriangleAux :
    Triangle (_root_.DerivedCategory (ModuleCat.{u + 1} Λ)) :=
  Φ.mapTriangle.obj (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).mapTriangle.obj
    (_root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n))

omit [Φ.Linear Λ] in
lemma reductionTriangleAux_distinguished :
    reductionTriangleAux hϖ n Φ K ∈ distTriang _ :=
  Φ.map_distinguished _ (Functor.map_distinguished _ _
    (_root_.DerivedCategory.quotPowTriangle_distinguished _ hϖ rfl n))

omit [Φ.IsTriangulated] in
lemma reductionTriangleAux_mor₁ :
    (reductionTriangleAux hϖ n Φ K).mor₁ = ϖ ^ n • 𝟙 _ := by
  change Φ.map (((derivedTensor (ModuleCat.{u + 1} Λ) X).obj K).map
    (_root_.DerivedCategory.quotPowTriangle X.smallEtaleTopology hϖ rfl n).mor₁) = _
  rw [_root_.DerivedCategory.quotPowTriangle_mor₁, Functor.map_smul,
    CategoryTheory.Functor.map_id, Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- The identification `Φ(K ⊗ᴸ Λ_X) ≅ Φ(K)`. -/
noncomputable abbrev reductionTriangleUnitIso :
    (reductionTriangleAux hϖ n Φ K).obj₁ ≅ Φ.obj K :=
  Φ.mapIso (derivedTensorSingleUnitIso K)

/-- The second morphism `Φ(K) ⟶ Φ(K_n)` of the reduction triangle. -/
noncomputable def reductionTriangleMor₂ :
    Φ.obj K ⟶ Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) :=
  (reductionTriangleUnitIso hϖ n Φ K).inv ≫ (reductionTriangleAux hϖ n Φ K).mor₂

/-- The third morphism `Φ(K_n) ⟶ Φ(K)⟦1⟧` of the reduction triangle. -/
noncomputable def reductionTriangleMor₃ :
    Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) ⟶ (Φ.obj K)⟦(1 : ℤ)⟧ :=
  (reductionTriangleAux hϖ n Φ K).mor₃ ≫ (reductionTriangleUnitIso hϖ n Φ K).hom⟦(1 : ℤ)⟧'

/-- The distinguished triangle `Φ(K) ⟶[ϖⁿ] Φ(K) ⟶ Φ(K_n) ⟶ Φ(K)⟦1⟧`, for a triangulated
`Λ`-linear functor `Φ`. -/
lemma reductionTriangle_distinguished :
    Triangle.mk (ϖ ^ n • 𝟙 (Φ.obj K)) (reductionTriangleMor₂ hϖ n Φ K)
      (reductionTriangleMor₃ hϖ n Φ K) ∈ distTriang _ := by
  let e := reductionTriangleUnitIso hϖ n Φ K
  refine isomorphic_distinguished _ (reductionTriangleAux_distinguished hϖ n Φ K) _
    (Triangle.isoMk _ _ e.symm e.symm (Iso.refl _) ?_ ?_ ?_)
  · change (ϖ ^ n • 𝟙 _) ≫ e.inv = e.inv ≫ (reductionTriangleAux hϖ n Φ K).mor₁
    rw [reductionTriangleAux_mor₁, Linear.smul_comp, Linear.comp_smul, Category.id_comp,
      Category.comp_id]
  · change reductionTriangleMor₂ hϖ n Φ K ≫ 𝟙 _ = e.inv ≫ _
    rw [Category.comp_id]
    rfl
  · change reductionTriangleMor₃ hϖ n Φ K ≫ e.inv⟦(1 : ℤ)⟧' = 𝟙 _ ≫ _
    rw [reductionTriangleMor₃, Category.assoc, ← Functor.map_comp, Iso.hom_inv_id,
      CategoryTheory.Functor.map_id, Category.comp_id, Category.id_comp]

/-- The identification `Λ ⧸ (ϖⁿ) ≅ Λ ⧸ (ϖ)ⁿ`. -/
noncomputable abbrev quotSpanPowLinearEquiv :
    (Λ ⧸ Ideal.span {ϖ ^ n}) ≃ₗ[Λ] (Λ ⧸ Ideal.span {ϖ} ^ n) :=
  Submodule.quotEquivOfEq _ _ (Ideal.span_singleton_pow ϖ n).symm

/-- The identification of the `ϖⁿ`-torsion `M[ϖⁿ]` with `Tor₁(M, Λ ⧸ (ϖ)ⁿ)`. -/
noncomputable def torsionByIsoTor (M : ModuleCat.{u + 1} Λ) :
    ModuleCat.of Λ (Submodule.torsionBy Λ M (ϖ ^ n)) ≅
      ((Tor (ModuleCat.{u + 1} Λ) 1).obj M).obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  (ModuleCat.torOneQuotSpanSingletonIso (pow_mem hϖ n) M).symm ≪≫
    ((Tor (ModuleCat.{u + 1} Λ) 1).obj M).mapIso (quotSpanPowLinearEquiv n).toModuleIso

/-- Blueprint `prop-pod-integral-degreewise-form`: the universal coefficient sequence of a
triangulated `Λ`-linear functor `Φ : D(X_ét, Λ) ⥤ D(Λ)`,

`Hⁱ(Φ K) ⊗_Λ Λ/(ϖ)ⁿ ⟶ Hⁱ(Φ K_n) ⟶ Tor₁^Λ(Hⁱ⁺¹(Φ K), Λ/(ϖ)ⁿ)`,

for `K_n = K ⊗ᴸ (Λ/(ϖ)ⁿ)_X`: the universal coefficient sequence
(`DerivedCategory.universalCoefficientSequence`) of the distinguished triangle
`Φ(K) ⟶[ϖⁿ] Φ(K) ⟶ Φ(K_n) ⟶ Φ(K)⟦1⟧`, with the `ϖⁿ`-torsion identified with the Tor term. -/
noncomputable def reductionSequence (i : ℤ) : ShortComplex (ModuleCat.{u + 1} Λ) :=
  (_root_.DerivedCategory.universalCoefficientSequence
    (reductionTriangle_distinguished hϖ n Φ K) i (i + 1) rfl).transport
    (TensorProduct.congr (LinearEquiv.refl Λ _) (quotSpanPowLinearEquiv n)).toModuleIso
    (Iso.refl _) (torsionByIsoTor hϖ n _)

lemma reductionSequence_X₁ (i : ℤ) :
    (reductionSequence hϖ n Φ K i).X₁ = ModuleCat.of Λ
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj (Φ.obj K) ⊗[Λ]
        (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

lemma reductionSequence_X₂ (i : ℤ) :
    (reductionSequence hϖ n Φ K i).X₂ =
      (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
        (Φ.obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K)) :=
  rfl

lemma reductionSequence_X₃ (i : ℤ) :
    (reductionSequence hϖ n Φ K i).X₃ = ((Tor (ModuleCat.{u + 1} Λ) 1).obj
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (i + 1)).obj
        (Φ.obj K))).obj (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

/-- Blueprint `prop-pod-integral-degreewise-form`: the universal coefficient sequence
`0 ⟶ Hⁱ(Φ K) ⊗ Λ/(ϖ)ⁿ ⟶ Hⁱ(Φ K_n) ⟶ Tor₁(Hⁱ⁺¹(Φ K), Λ/(ϖ)ⁿ) ⟶ 0` of a triangulated `Λ`-linear
functor `Φ` is short exact. -/
theorem shortExact_reductionSequence (i : ℤ) : (reductionSequence hϖ n Φ K i).ShortExact :=
  (_root_.DerivedCategory.universalCoefficientSequence_shortExact _ _ _ _).transport _ _ _

/-- Blueprint `prop-pod-integral-degreewise-form`: if `Hⁱ⁺¹(Φ K)` is flat (for example finite
projective), the Tor term vanishes and `Hⁱ(Φ K) ⊗ Λ/(ϖ)ⁿ ⟶ Hⁱ(Φ K_n)` is an isomorphism. -/
theorem isIso_reductionSequence_f (i : ℤ)
    (hflat : Module.Flat Λ
      ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (i + 1)).obj
        (Φ.obj K))) :
    IsIso (reductionSequence hϖ n Φ K i).f :=
  (shortExact_reductionSequence hϖ n Φ K i).isIso_f_iff.2
    ((ModuleCat.isZero_torsionBy_of_flat (pow_mem hϖ n) _ hflat).of_iso
      (torsionByIsoTor hϖ n _).symm)

end Reduction

section CompactSupport

variable {Λ : Type (u + 1)} [CommRing Λ] {X Y : Scheme.{u}} {ϖ : Λ}
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (a : X ⟶ Y) [HasCompactification a]
  (K : DerivedCategoryModule Λ X)

/-- Blueprint `prop-pod-integral-degreewise-form`: the universal coefficient sequence of
compactly supported cohomology,

`Hⁱ_c(X, K) ⊗_Λ Λ/(ϖ)ⁿ ⟶ Hⁱ_c(X, K_n) ⟶ Tor₁^Λ(Hⁱ⁺¹_c(X, K), Λ/(ϖ)ⁿ)`,

for `K_n = K ⊗ᴸ (Λ/(ϖ)ⁿ)_X`. -/
noncomputable abbrev compactlySupportedReductionSequence (i : ℤ) :
    ShortComplex (ModuleCat.{u + 1} Λ) :=
  reductionSequence hϖ n (compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a) K i

lemma compactlySupportedReductionSequence_X₁ (i : ℤ) :
    (compactlySupportedReductionSequence hϖ n a K i).X₁ =
      ModuleCat.of Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K ⊗[Λ] (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

lemma compactlySupportedReductionSequence_X₂ (i : ℤ) :
    (compactlySupportedReductionSequence hϖ n a K i).X₂ =
      (H_c(a)[ModuleCat.{u + 1} Λ](i)).obj ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj K) :=
  rfl

lemma compactlySupportedReductionSequence_X₃ (i : ℤ) :
    (compactlySupportedReductionSequence hϖ n a K i).X₃ =
      ((Tor (ModuleCat.{u + 1} Λ) 1).obj ((H_c(a)[ModuleCat.{u + 1} Λ](i + 1)).obj K)).obj
        (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the first
variable).

For a nonzerodivisor `ϖ` of `Λ` (a uniformizer of `𝒪_E`, `A_{E,n} = Λ/(ϖ)ⁿ`) and
`K ∈ D(X_ét, Λ)`, the universal coefficient sequence

`0 ⟶ Hⁱ_c(X, K) ⊗_Λ A_{E,n} ⟶ Hⁱ_c(X, K_n) ⟶ Tor₁^Λ(Hⁱ⁺¹_c(X, K), A_{E,n}) ⟶ 0`

is short exact. The blueprint assumes `K` perfect; the sequence exists for every `K`. -/
theorem shortExact_compactlySupportedReductionSequence (i : ℤ) :
    (compactlySupportedReductionSequence hϖ n a K i).ShortExact :=
  shortExact_reductionSequence hϖ n _ K i

/-- Blueprint `prop-pod-integral-degreewise-form`: if `Hⁱ⁺¹_c(X, K)` is flat (for example finite
projective), the Tor term vanishes and `Hⁱ_c(X, K) ⊗_Λ A_{E,n} ≅ Hⁱ_c(X, K_n)`. -/
theorem isIso_compactlySupportedReductionSequence_f (i : ℤ)
    (hflat : Module.Flat Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i + 1)).obj K)) :
    IsIso (compactlySupportedReductionSequence hϖ n a K i).f :=
  isIso_reductionSequence_f hϖ n _ K i hflat

end CompactSupport

section Ordinary

variable {Λ : Type (u + 1)} [CommRing Λ] {X : Scheme.{u}} {ϖ : Λ}
  (hϖ : ϖ ∈ nonZeroDivisors Λ) (n : ℕ) (L : DerivedCategoryModule Λ X)

/-- Blueprint `prop-pod-integral-degreewise-form`: the universal coefficient sequence of
ordinary cohomology, for the second variable `L = K^∨(d)` of the Poincaré pairing,

`Hʲ(X, L) ⊗_Λ Λ/(ϖ)ⁿ ⟶ Hʲ(X, L_n) ⟶ Tor₁^Λ(Hʲ⁺¹(X, L), Λ/(ϖ)ⁿ)`. -/
noncomputable abbrev cohomologyReductionSequence (j : ℤ) : ShortComplex (ModuleCat.{u + 1} Λ) :=
  reductionSequence hϖ n (rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) X) L j

lemma cohomologyReductionSequence_X₁ (j : ℤ) :
    (cohomologyReductionSequence hϖ n L j).X₁ =
      ModuleCat.of Λ ((cohomology (ModuleCat.{u + 1} Λ) X j).obj L ⊗[Λ]
        (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

lemma cohomologyReductionSequence_X₂ (j : ℤ) :
    (cohomologyReductionSequence hϖ n L j).X₂ =
      (cohomology (ModuleCat.{u + 1} Λ) X j).obj
        ((reductionModIdeal Λ X (Ideal.span {ϖ} ^ n)).obj L) :=
  rfl

lemma cohomologyReductionSequence_X₃ (j : ℤ) :
    (cohomologyReductionSequence hϖ n L j).X₃ =
      ((Tor (ModuleCat.{u + 1} Λ) 1).obj ((cohomology (ModuleCat.{u + 1} Λ) X (j + 1)).obj L)).obj
        (ModuleCat.of Λ (Λ ⧸ Ideal.span {ϖ} ^ n)) :=
  rfl

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the second
variable).

For the second variable `L = K^∨(d)` of the Poincaré pairing (or any `L ∈ D(X_ét, Λ)`), the
universal coefficient sequence

`0 ⟶ Hʲ(X, L) ⊗_Λ A_{E,n} ⟶ Hʲ(X, L_n) ⟶ Tor₁^Λ(Hʲ⁺¹(X, L), A_{E,n}) ⟶ 0`

is short exact. -/
theorem shortExact_cohomologyReductionSequence (j : ℤ) :
    (cohomologyReductionSequence hϖ n L j).ShortExact :=
  shortExact_reductionSequence hϖ n _ L j

/-- Blueprint `prop-pod-integral-degreewise-form`: if `Hʲ⁺¹(X, L)` is flat (for example finite
projective), the Tor term vanishes and `Hʲ(X, L) ⊗_Λ A_{E,n} ≅ Hʲ(X, L_n)`. -/
theorem isIso_cohomologyReductionSequence_f (j : ℤ)
    (hflat : Module.Flat Λ ((cohomology (ModuleCat.{u + 1} Λ) X (j + 1)).obj L)) :
    IsIso (cohomologyReductionSequence hϖ n L j).f :=
  isIso_reductionSequence_f hϖ n _ L j hflat

end Ordinary

section Duality

variable {k : Type u} [Field k] [IsSepClosed k] {Λ : Type (u + 1)} [CommRing Λ]
  {X : Scheme.{u}} (a : X ⟶ Spec (.of k)) [HasCompactification a]
  {G : DerivedCategoryModule Λ (Spec (.of k)) ⥤ DerivedCategoryModule Λ X} {d : ℕ}

/-- The cohomology `H^{2d-i}(X, L)` of the second variable is the `(-i)`-th cohomology of
`RΓ(Spec k, Ra_* L[2d])`. -/
noncomputable def cohomologyIsoHomologyShift (L : DerivedCategoryModule Λ X) (i : ℤ) :
    (cohomology (ModuleCat.{u + 1} Λ) X (2 * d - i)).obj L ≅
      (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).obj
        ((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).obj
          (((R((a)_*[ModuleCat.{u + 1} Λ])).obj L)⟦(2 * d : ℤ)⟧)) :=
  (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (2 * d - i)).mapIso
      ((rightDerivedLowerStarCompRightDerivedGlobalSectionsIso _ a).app _).symm ≪≫
    (((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) 0).shiftIso (2 * d : ℤ)
      (-i) (2 * d - i) (by ring)).app _).symm ≪≫
    (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso
      (((rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))).commShiftIso
        (2 * d : ℤ)).app _).symm

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the degreewise
duality, non-canonical form).

Let `k` be separably closed, `Λ` a commutative ring (the integral stage `𝒪_E`),
`γ : T[2d] ≅ Ra^! Λ` a purity isomorphism, for any right adjoint `Ra^!` of `Ra_!` (for
`T = Λ_X(d)`, so that `K^∨ ⊗ᴸ T = K^∨(d)`), and
`K` perfect over `Λ_X`. If `RΓ_c(X, K)` is a perfect complex of `Λ`-modules and its cohomology
modules `Hʲ_c(X, K)` are finite projective, then for every `i` the module
`H^{2d-i}(X, K^∨(d))` is finite projective and

`H^{2d-i}(X, K^∨(d)) ≅ Hom_Λ(Hⁱ_c(X, K), Λ)`.

It follows from the perfectness of the derived Poincaré pairing at `Λ`
(`AlgebraicGeometry.Etale.isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable`),
`RΓ(X, K^∨(d))[2d] ≅ RΓ_c(X, K)^∨`, by taking `H^{-i}`, since `RΓ_c(X, K)` splits as the sum
of its projective cohomology modules (`DerivedCategory.nonempty_iso_homology_ihom_of_projective`).
As for `AlgebraicGeometry.Etale.TateOrientation.degreewise_duality`, only an abstract
isomorphism is proved (see the implementation notes of this file). The Tor terms of the
universal coefficient sequences of both variables then vanish
(`AlgebraicGeometry.Etale.isIso_compactlySupportedReductionSequence_f`,
`AlgebraicGeometry.Etale.isIso_cohomologyReductionSequence_f`). -/
theorem integralDegreewiseDuality (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G)
    {T : DerivedCategoryModule Λ X} (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : DerivedCategoryModule Λ X} (hKd : IsDualizable K)
    (hperf : ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K).IsPerfect)
    (hproj : ∀ j, Module.Projective Λ ((H_c(a)[ModuleCat.{u + 1} Λ](j)).obj K) ∧
      Module.Finite Λ ((H_c(a)[ModuleCat.{u + 1} Λ](j)).obj K)) (i : ℤ) :
    Module.Projective Λ ((cohomology (ModuleCat.{u + 1} Λ) X (2 * d - i)).obj
        (((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T)) ∧
      Module.Finite Λ ((cohomology (ModuleCat.{u + 1} Λ) X (2 * d - i)).obj
        (((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T)) ∧
      Nonempty ((cohomology (ModuleCat.{u + 1} Λ) X (2 * d - i)).obj
          (((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj T) ≅
        ModuleCat.of Λ (Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))) := by
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  let C := (R(a)_![ModuleCat.{u + 1} Λ]).obj K
  have hb := isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a adj γ hKd
  obtain ⟨eA⟩ := (nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence _ _
    C).map fun e ↦ RΓ.mapIso hb.iso ≪≫ e
  obtain ⟨a', b', hab⟩ := hperf.exists_homologyConcentratedIn
  obtain ⟨eB⟩ := _root_.DerivedCategory.nonempty_iso_homology_ihom_of_projective hab.1 hab.2
    hproj i
  let e := cohomologyIsoHomologyShift a (d := d) _ i ≪≫
    (_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso eA ≪≫ eB
  have := (hproj i).1
  have := (hproj i).2
  exact ⟨Module.Projective.of_equiv (M := Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))
      e.toLinearEquiv.symm,
    Module.Finite.equiv (M := Module.Dual Λ ((H_c(a)[ModuleCat.{u + 1} Λ](i)).obj K))
      e.toLinearEquiv.symm, ⟨e⟩⟩

/-- Blueprint `prop-pod-integral-degreewise-form`: Integral degreewise form (the adjoint maps).

In the situation of `AlgebraicGeometry.Etale.integralDegreewiseDuality`, without any
projectivity assumption: the dual `RΓ_c(X, K)^∨` has universal coefficient sequences
`0 ⟶ H^{-i}(RΓ_c(X, K)^∨) ⊗ Λ/(ϖⁿ) ⟶ H^{-i}(D) ⟶ H^{1-i}(RΓ_c(X, K)^∨)[ϖⁿ] ⟶ 0` for every
reduction triangle `RΓ_c(X, K)^∨ ⟶[ϖⁿ] RΓ_c(X, K)^∨ ⟶ D ⟶ RΓ_c(X, K)^∨⟦1⟧` (for instance
`D = RΓ_c(X, K)^∨ ⊗ᴸ Λ/(ϖⁿ)`), and the adjoint of the derived Poincaré pairing identifies the
cohomology of `RΓ_c(X, K)^∨` with that of the second variable,
`H^{-i}(RΓ_c(X, K)^∨) ≅ H^{2d-i}(X, K^∨(d))`, so that these sequences correspond to the
sequences of the second variable
(`AlgebraicGeometry.Etale.shortExact_cohomologyReductionSequence`). -/
theorem integralDegreewise_adjoint (adj : R(a)_![ModuleCat.{u + 1} Λ] ⊣ G)
    {T : DerivedCategoryModule Λ X} (γ : T⟦(2 * d : ℤ)⟧ ≅ G.obj (𝟙_ _))
    {K : DerivedCategoryModule Λ X} (hKd : IsDualizable K) {ϖ : Λ} (n : ℕ)
    {D : _root_.DerivedCategory (ModuleCat.{u + 1} Λ)}
    {g : (ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)).obj
      (𝟙_ _) ⟶ D}
    {h : D ⟶ ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)).obj
      (𝟙_ _))⟦(1 : ℤ)⟧}
    (hT : Triangle.mk (ϖ ^ n • 𝟙 _) g h ∈ distTriang _) (i : ℤ) :
    (_root_.DerivedCategory.universalCoefficientSequence hT (-i) (-i + 1) rfl).ShortExact ∧
      Nonempty ((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).obj
          ((ihom ((compactlySupportedGlobalSections (ModuleCat.{u + 1} Λ) a).obj K)).obj
            (𝟙_ _)) ≅
        (cohomology (ModuleCat.{u + 1} Λ) X (2 * d - i)).obj
          (((derivedTensor _ X).obj ((DerivedCategory.coefficientDual _ X).obj (op K))).obj
            T)) := by
  refine ⟨_root_.DerivedCategory.universalCoefficientSequence_shortExact _ _ _ _, ?_⟩
  let RΓ := rightDerivedGlobalSections (ModuleCat.{u + 1} Λ) (Spec (.of k))
  have hb := isPerfectPairing_poincarePairing_of_isSepClosed_of_isDualizable a adj γ hKd
  obtain ⟨eA⟩ := (nonempty_iso_rightDerivedGlobalSections_coefficientDual_of_isEquivalence _ _
    ((R(a)_![ModuleCat.{u + 1} Λ]).obj K)).map fun e ↦ RΓ.mapIso hb.iso ≪≫ e
  exact ⟨((_root_.DerivedCategory.homologyFunctor (ModuleCat.{u + 1} Λ) (-i)).mapIso eA.symm ≪≫
    (cohomologyIsoHomologyShift a (d := d) _ i).symm)⟩

end Duality

end Etale

end AlgebraicGeometry
