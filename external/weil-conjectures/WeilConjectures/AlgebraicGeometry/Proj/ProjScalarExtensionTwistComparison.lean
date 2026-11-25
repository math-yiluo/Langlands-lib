/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Compactification.NagataAffineProjScalarExtension
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.Modules
public import WeilConjectures.AlgebraicGeometry.ProjectiveSpectrum.Twist.UnitToTwist
public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackSectionAdjunction
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.CochainTensorUniverses
public import WeilConjectures.Algebra.Homology.Site.SiteTensorFunctorialitySupplement
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.Mathlib.Algebra.Homology.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProductOfUniverses
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistExistence
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistFractionLaws
import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistCompositionLaw
import Mathlib.RingTheory.TensorProduct.Maps
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # Scalar extension of arbitrary Proj twists

The fraction normalization is stated using the existing pointwise realization of twists.
Multiplying by the denominator avoids choosing a representative in a localization.
The product law is stated on local sections, which generate the sheaf tensor product.

## References

* Stacks 01N2(3), 01MY, 01MZ
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

private theorem scalarExtension_twist_homogeneousSection
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ) (r : Proj ℬ ⟶ Proj 𝒜)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ)
    (n : ℕ) (a : A) (ha : a ∈ 𝒜 n) :
    scalarExtensionTwistSection r θ (0 + n) ⊤
      ((unitToTwist ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
      (twist ℬ (0 + n)).presheaf.map
        (homOfLE (le_top : r ⁻¹ᵁ ⊤ ≤ ⊤)).op
        ((unitToTwist (ψ.map_mem ha)).app ⊤ (1 : Γ(Proj ℬ, ⊤))) := by
  apply Subtype.ext
  funext x
  apply Subtype.ext
  have hx := hθ (0 + n) n 0 a 1 ha (SetLike.one_mem_graded 𝒜) (by simp) ⊤
    (by intro y hy; exact y.asHomogeneousIdeal.toIdeal.one_notMem)
    ((unitToTwist ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤)))
    (by intro y; simp [val_unitToTwist_app_apply, Localization.mk_one]) 1 x
  simpa [val_unitToTwist_app_apply, Localization.mk_one] using hx

private theorem scalarExtension_twist_coefficientComposition
    {R S A B T C : Type u}
    [CommRing R] [CommRing S] [CommRing A] [CommRing B] [CommRing T] [CommRing C]
    [Algebra R S] [Algebra R A] [Algebra S B]
    [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra T C]
    {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule S B}
    {𝒞 : ℕ → Submodule T C} [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (γ : TensorProduct S T B ≃ₐ[T] C) (χ : ℬ →+*ᵍ 𝒞)
    (hγχ : ∀ b : B, γ (TensorProduct.tmul S (1 : T) b) = χ b)
    (h𝒞 : ∀ n : ℕ, 𝒞 n = Submodule.span T (χ '' (ℬ n : Set B))) :
    ∃ δ : TensorProduct R T A ≃ₐ[T] C,
      (∀ (t : T) (a : A), δ (TensorProduct.tmul R t a) = t • χ (ψ a)) ∧
      (∀ n : ℕ, 𝒞 n = Submodule.span T ((χ.comp ψ) '' (𝒜 n : Set A))) := by
  have hγχt (t : T) (b : B) : γ (TensorProduct.tmul S t b) = t • χ b := by
    calc
      γ (TensorProduct.tmul S t b) =
          γ (t • TensorProduct.tmul S (1 : T) b) := by
        congr 1
        simp [TensorProduct.smul_tmul']
      _ = t • γ (TensorProduct.tmul S (1 : T) b) := γ.toLinearEquiv.map_smul t _
      _ = t • χ b := by rw [hγχ]
  let δ : TensorProduct R T A ≃ₐ[T] C :=
    (Algebra.TensorProduct.cancelBaseChange R S T T A).symm |>.trans
      ((Algebra.TensorProduct.congr (AlgEquiv.refl : T ≃ₐ[T] T) β).trans γ)
  refine ⟨δ, ?_, ?_⟩
  · intro t a
    simp only [δ, AlgEquiv.trans_apply, Algebra.TensorProduct.cancelBaseChange_symm_tmul,
      Algebra.TensorProduct.congr_apply, Algebra.TensorProduct.map_tmul,
      AlgEquiv.coe_toAlgHom, hβψ, hγχt]
    rfl
  · intro n
    rw [h𝒞 n]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro _ ⟨b, hb, rfl⟩
      rw [hgraded n] at hb
      induction hb using Submodule.span_induction with
      | mem b hb =>
          obtain ⟨a, ha, rfl⟩ := hb
          exact Submodule.subset_span ⟨a, ha, rfl⟩
      | zero =>
          change χ 0 ∈ Submodule.span T ((χ.comp ψ) '' (𝒜 n : Set A))
          rw [map_zero]
          exact Submodule.zero_mem _
      | add b c hb hc ihb ihc =>
          change χ (b + c) ∈ Submodule.span T ((χ.comp ψ) '' (𝒜 n : Set A))
          rw [map_add]
          exact Submodule.add_mem _ ihb ihc
      | smul s b hb ih =>
          have hs : χ (s • b) = (algebraMap S T s) • χ b := by
            rw [← hγχ (s • b), TensorProduct.tmul_smul, TensorProduct.smul_tmul',
              Algebra.smul_def, mul_one, hγχt]
          rw [hs]
          exact Submodule.smul_mem _ _ ih
    · apply Submodule.span_le.mpr
      rintro _ ⟨a, ha, rfl⟩
      exact Submodule.subset_span ⟨ψ a, ψ.map_mem ha, rfl⟩

private theorem scalarExtension_irrelevant_le
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R A] [Algebra S B]
    {𝒜 : ℕ → Submodule R A} {ℬ : ℕ → Submodule S B}
    [GradedRing 𝒜] [GradedRing ℬ] (ψ : 𝒜 →+*ᵍ ℬ)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A))) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
  change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ _
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro n hn b hb
  rw [hgraded n] at hb
  induction hb using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      exact Ideal.mem_map_of_mem ψ (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)
  | zero => exact Ideal.zero_mem _
  | add x y hx hy ihx ihy => exact Ideal.add_mem _ ihx ihy
  | smul s x hx ih =>
      rw [Algebra.smul_def]
      exact Ideal.mul_mem_left _ _ ih

private theorem scalarExtension_eq_map
    {A B : Type u} [CommRing A] [CommRing B]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ B] [AddSubgroupClass τ B]
    {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ)
    (r : Proj ℬ ⟶ Proj 𝒜)
    (hchart : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
      awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
          awayι 𝒜 f hf hn) : r = Proj.map ψ hψ := by
  apply (Proj.mapAffineOpenCover ψ hψ).openCover.hom_ext
  intro i
  exact (hchart i.1 i.2 i.2.2 i.1.2).trans
    (Proj.awayι_comp_map ψ hψ i.1.2 i.2 i.2.2).symm

/-- Scalar extension preserves every twist, with its fraction, algebra, section and
composition normalizations. -/
theorem scalarExtension_twist_comparison
    {R S A B : Type u} [CommRing R] [CommRing S] [CommRing A] [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ρA : R →+* 𝒜 0) (ρB : S →+* ℬ 0)
    (hρA : ∀ a : R, (ρA a : A) = algebraMap R A a)
    (hρB : ∀ b : S, (ρB b : B) = algebraMap S B b)
    (β : TensorProduct R S A ≃ₐ[S] B) (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A)))
    (r : Proj ℬ ⟶ Proj 𝒜)
    (hpre : ∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
      r ⁻¹ᵁ basicOpen 𝒜 f = basicOpen ℬ (ψ f))
    (hchart : ∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
      awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
        Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
          awayι 𝒜 f hf hn) :
    ∃ θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
      IsScalarExtensionTwistComparison ψ r θ ∧
      (∀ θ' : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j,
        IsScalarExtensionTwistComparison ψ r θ' → θ' = θ) ∧
      (∀ (i j : ℤ) (U : (Proj 𝒜).Opens)
        (s : Γ(twist 𝒜 i, U)) (t : Γ(twist 𝒜 j, U))
        (v : Γ(twist 𝒜 (i + j), U)),
        (∀ x : U, (v.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          (s.1 x : Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) * t.1 x) →
        ∀ x : r ⁻¹ᵁ U,
          ((scalarExtensionTwistSection r θ (i + j) U v).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) =
          ((scalarExtensionTwistSection r θ i U s).1 x :
            Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal) *
          (scalarExtensionTwistSection r θ j U t).1 x) ∧
      (∀ (U : (Proj 𝒜).Opens) (s : Γ(Proj 𝒜, U)),
        scalarExtensionTwistSection r θ 0 U
          (Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := 𝒜)) U s) =
          Scheme.Modules.Hom.app (unitToTwistZero (𝒜 := ℬ)) (r ⁻¹ᵁ U) (r.app U s)) ∧
      (∀ (n : ℕ) (a : A) (ha : a ∈ 𝒜 n),
        scalarExtensionTwistSection r θ (0 + n) ⊤
          ((unitToTwist ha).app ⊤ (1 : Γ(Proj 𝒜, ⊤))) =
          (twist ℬ (0 + n)).presheaf.map
            (homOfLE (le_top : r ⁻¹ᵁ ⊤ ≤ ⊤)).op
            ((unitToTwist (ψ.map_mem ha)).app ⊤ (1 : Γ(Proj ℬ, ⊤)))) ∧
      (∀ {T C : Type u} [CommRing T] [CommRing C]
        [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra T C]
        (𝒞 : ℕ → Submodule T C) [GradedRing 𝒞]
        (γ : TensorProduct S T B ≃ₐ[T] C) (χ : ℬ →+*ᵍ 𝒞),
        (∀ b : B, γ (TensorProduct.tmul S (1 : T) b) = χ b) →
        (∀ n : ℕ, 𝒞 n = Submodule.span T (χ '' (ℬ n : Set B))) →
        (∃ δ : TensorProduct R T A ≃ₐ[T] C,
          (∀ (t : T) (a : A), δ (TensorProduct.tmul R t a) = t • χ (ψ a)) ∧
          (∀ n : ℕ, 𝒞 n = Submodule.span T ((χ.comp ψ) '' (𝒜 n : Set A)))) ∧
        ∀ (q : Proj 𝒞 ⟶ Proj ℬ) (p : Proj 𝒞 ⟶ Proj 𝒜),
          (∀ (n : ℕ) (f : B) (hf : f ∈ ℬ n) (hn : 0 < n),
            awayι 𝒞 (χ f) (χ.map_mem hf) hn ≫ q =
              Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map χ f)) ≫
                awayι ℬ f hf hn) →
          (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
            awayι 𝒞 (χ (ψ f)) ((χ.comp ψ).map_mem hf) hn ≫ p =
              Spec.map (CommRingCat.ofHom
                (HomogeneousLocalization.Away.map (χ.comp ψ) f)) ≫ awayι 𝒜 f hf hn) →
          ∀ (η : ∀ j : ℤ, (tensorPullback q).obj (twist ℬ j) ≅ twist 𝒞 j)
            (ζ : ∀ j : ℤ, (tensorPullback p).obj (twist 𝒜 j) ≅ twist 𝒞 j),
            IsScalarExtensionTwistComparison χ q η →
            IsScalarExtensionTwistComparison (χ.comp ψ) p ζ →
            ∃ hp : p = q ≫ r, ∀ j : ℤ,
              ζ j = eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (twist 𝒜 j)) hp) ≪≫
                (tensorPullbackSectionComp q r).app (twist 𝒜 j) ≪≫
                (tensorPullback q).mapIso (θ j) ≪≫ η j) ∧
      (∀ ι : ∀ j : ℤ, (tensorPullback (𝟙 (Proj 𝒜))).obj (twist 𝒜 j) ≅ twist 𝒜 j,
        IsScalarExtensionTwistComparison (GradedRingHom.id 𝒜) (𝟙 (Proj 𝒜)) ι →
        ∀ j : ℤ, ι j = (tensorPullbackSectionId (Proj 𝒜)).app (twist 𝒜 j)) := by
  obtain ⟨θ, hθ⟩ := scalarExtension_twist_exists 𝒜 ℬ β ψ hβψ hgraded r hchart
  obtain ⟨hu, hm, hz, hi⟩ := scalarExtension_twist_fraction_laws 𝒜 ℬ ψ r θ hθ
  refine ⟨θ, hθ, hu, hm, hz, ?_, ?_, hi⟩
  · intro n a ha
    exact scalarExtension_twist_homogeneousSection ψ r θ hθ n a ha
  · intro T C _ _ _ _ _ _ 𝒞 _ γ χ hγχ h𝒞
    refine ⟨scalarExtension_twist_coefficientComposition β ψ hβψ hgraded γ χ hγχ h𝒞, ?_⟩
    intro q p hq hp η ζ hη hζ
    have hψ := scalarExtension_irrelevant_le ψ hgraded
    have hχ := scalarExtension_irrelevant_le χ h𝒞
    have hcomp := HomogeneousIdeal.irrelevant_le_map_comp hψ hχ
    have he : p = q ≫ r := by
      rw [scalarExtension_eq_map (χ.comp ψ) hcomp p hp,
        scalarExtension_eq_map χ hχ q hq, scalarExtension_eq_map ψ hψ r hchart,
        Proj.map_comp]
    refine ⟨he, ?_⟩
    exact scalarExtension_twist_composition_law
      𝒜 ℬ ρA ρB hρA hρB β ψ hβψ hgraded r hpre hchart θ hθ
      𝒞 γ χ hγχ h𝒞 q p hq hp η ζ hη hζ he

end AlgebraicGeometry.Proj
