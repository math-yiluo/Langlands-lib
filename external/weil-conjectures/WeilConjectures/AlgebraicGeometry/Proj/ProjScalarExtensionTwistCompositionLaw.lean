/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Proj.ProjScalarExtensionTwistData
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-! # ProjScalarExtensionTwistCompositionLaw

## References

* Stacks Project, Constructions, Tags 01N2, 01MY and 01MZ
* Stacks Project, Constructions, Tag 01MZ, with 01MY and 01N2
-/

@[expose] public section

set_option autoImplicit false
set_option relaxedAutoImplicit false

universe u

open CategoryTheory Opposite TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Proj

attribute [local irreducible] tensorPullback tensorPullbackObj tensorPullbackSection

private theorem section_unit {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionAdjunction f).unit.app M).app U s =
      tensorPullbackSection f M U s :=
  (Classical.choose_spec (existsUnique_tensorPullbackSectionAdjunction f)).1 M U s

private theorem section_naturality {X Y : Scheme.{u}} (f : X ⟶ Y)
    {M N : Y.Modules} (v : M ⟶ N) (U : Y.Opens) (s : Γ(M, U)) :
    ((tensorPullback f).map v).app (f ⁻¹ᵁ U) (tensorPullbackSection f M U s) =
      tensorPullbackSection f N U (v.app U s) := by
  rw [← section_unit, ← section_unit]
  exact (congrArg (fun k ↦ k.app U s)
    ((tensorPullbackSectionAdjunction f).unit.naturality v)).symm

private theorem section_comp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (M : Z.Modules) (U : Z.Opens) (s : Γ(M, U)) :
    ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
        (tensorPullbackSection (f ≫ g) M U s) =
      tensorPullbackSection f ((tensorPullback g).obj M) (g ⁻¹ᵁ U)
        (tensorPullbackSection g M U s) := by
  have hu := Adjunction.unit_leftAdjointUniq_hom_app
    (tensorPullbackSectionAdjunction (f ≫ g))
    (((tensorPullbackSectionAdjunction g).comp (tensorPullbackSectionAdjunction f)).ofNatIsoRight
      (pushforwardComp f g)) M
  have hv := congrArg (fun k ↦ k.app U s) hu
  simp only [Hom.comp_app, pushforward_map_app, ConcreteCategory.comp_apply,
    Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Adjunction.comp_unit_app,
    Functor.whiskerLeft_app, pushforwardComp_hom_app_app] at hv
  change ((tensorPullbackSectionComp f g).hom.app M).app ((f ≫ g) ⁻¹ᵁ U)
    (((tensorPullbackSectionAdjunction (f ≫ g)).unit.app M).app U s) =
    ((tensorPullbackSectionAdjunction f).unit.app ((tensorPullback g).obj M)).app
      (g ⁻¹ᵁ U) (((tensorPullbackSectionAdjunction g).unit.app M).app U s) at hv
  simpa only [section_unit] using hv

attribute [local irreducible] tensorPullbackSectionComp

private theorem irrelevant_le_of_span
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

private theorem eq_map_of_charts
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

private theorem fraction_mul_denominator
    {A : Type u} [CommRing A] {σ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    {𝒜 : ℕ → σ} [GradedRing 𝒜] {j : ℤ} {i k : ℕ}
    (a : 𝒜 i) (b : 𝒜 k) (h : (i : ℤ) = (k : ℤ) + j)
    (x : Proj 𝒜) (hb : (b : A) ∉ x.asHomogeneousIdeal.toIdeal) :
    (HomogeneousLocalization.degreePart.mk
      (x := x.asHomogeneousIdeal.toIdeal.primeCompl) a b hb h).val * Localization.mk (b : A) 1 =
        Localization.mk (a : A) 1 := by
  change Localization.mk (a : A) ⟨(b : A), hb⟩ * Localization.mk (b : A) 1 = _
  simpa only [Localization.mk_one_eq_algebraMap, Localization.mk_eq_mk'] using
    IsLocalization.mk'_spec (Localization.AtPrime x.asHomogeneousIdeal.toIdeal)
      (a : A) (⟨(b : A), hb⟩ : x.asHomogeneousIdeal.toIdeal.primeCompl)

private theorem twist_pullback_hom_ext
    {A C : Type u} [CommRing A] [CommRing C]
    {σ τ : Type u} [SetLike σ A] [AddSubgroupClass σ A]
    [SetLike τ C] [AddSubgroupClass τ C]
    {𝒜 : ℕ → σ} {𝒞 : ℕ → τ} [GradedRing 𝒜] [GradedRing 𝒞]
    (f : Proj 𝒞 ⟶ Proj 𝒜) (j : ℤ)
    (α β : (tensorPullback f).obj (twist 𝒜 j) ⟶ twist 𝒞 j)
    (h : ∀ (i k : ℕ) (a : A) (b : A), a ∈ 𝒜 i → b ∈ 𝒜 k →
      (i : ℤ) = (k : ℤ) + j →
      ∀ (U : (Proj 𝒜).Opens), U ≤ basicOpen 𝒜 b →
      ∀ (s : Γ(twist 𝒜 j, U)),
        (∀ y : U, (s.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
          Localization.mk b 1 = Localization.mk a 1) →
        α.app (f ⁻¹ᵁ U) (tensorPullbackSection f (twist 𝒜 j) U s) =
          β.app (f ⁻¹ᵁ U) (tensorPullbackSection f (twist 𝒜 j) U s)) : α = β := by
  apply ((tensorPullbackSectionAdjunction f).homEquiv _ _).injective
  let α' := (tensorPullbackSectionAdjunction f).homEquiv _ _ α
  let β' := (tensorPullbackSectionAdjunction f).homEquiv _ _ β
  change α' = β'
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  apply Subtype.ext
  funext x
  apply Subtype.ext
  obtain ⟨V, hxV, e, i, k, hik, a, b, hb, hs⟩ := s.2 ⟨f x.1, x.2⟩
  let t : Γ(twist 𝒜 j, V) := (twist 𝒜 j).presheaf.map e.op s
  have ht : ∀ y : V, (t.1 y : Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) *
      Localization.mk (b : A) 1 = Localization.mk (a : A) 1 := by
    intro y
    change ((s.1 (e y) : ProjectiveSpectrum.Twist.fiber 𝒜 j y.1) :
      Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) * _ = _
    exact (congrArg (fun z : ProjectiveSpectrum.Twist.fiber 𝒜 j y.1 ↦
      z.val * Localization.mk (b : A) 1) (hs y)).trans
        (fraction_mul_denominator a b hik y.1 (hb y))
  have heq := h i k a b a.2 b.2 hik V (fun y hy ↦ hb ⟨y, hy⟩) t ht
  have heq' : α'.app V t = β'.app V t := by
    change α.app (f ⁻¹ᵁ V)
      (((tensorPullbackSectionAdjunction f).unit.app (twist 𝒜 j)).app V t) =
        β.app (f ⁻¹ᵁ V)
          (((tensorPullbackSectionAdjunction f).unit.app (twist 𝒜 j)).app V t)
    simpa only [section_unit] using heq
  have hα := congrArg (fun z ↦ (z.1 ⟨x.1, hxV⟩).val)
    (Hom.app_presheaf_map α' e s)
  have hβ := congrArg (fun z ↦ (z.1 ⟨x.1, hxV⟩).val)
    (Hom.app_presheaf_map β' e s)
  have hlocal := congrArg (fun z ↦ (z.1 ⟨x.1, hxV⟩).val) heq'
  exact hα.symm.trans (hlocal.trans hβ)

-- Retain the scalar-extension interface although the fraction argument needs less data.
set_option linter.unusedVariables false in
/-- Normalized twist comparisons respect the geometric composition of scalar extensions.
This assertion assumes the scheme-composition equality, proved in the importing item.
It constructs no twist comparison and contains no coefficient associator. -/
theorem scalarExtension_twist_composition_law
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
          awayι 𝒜 f hf hn)
    (θ : ∀ j : ℤ, (tensorPullback r).obj (twist 𝒜 j) ≅ twist ℬ j)
    (hθ : IsScalarExtensionTwistComparison ψ r θ) :
    (∀ {T C : Type u} [CommRing T] [CommRing C]
        [Algebra S T] [Algebra R T] [IsScalarTower R S T] [Algebra T C]
        (𝒞 : ℕ → Submodule T C) [GradedRing 𝒞]
        (γ : TensorProduct S T B ≃ₐ[T] C) (χ : ℬ →+*ᵍ 𝒞),
        (∀ b : B, γ (TensorProduct.tmul S (1 : T) b) = χ b) →
        (∀ n : ℕ, 𝒞 n = Submodule.span T (χ '' (ℬ n : Set B))) →
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
            ∀ hp : p = q ≫ r, ∀ j : ℤ,
              ζ j = eqToIso (congrArg (fun f ↦ (tensorPullback f).obj (twist 𝒜 j)) hp) ≪≫
                (tensorPullbackSectionComp q r).app (twist 𝒜 j) ≪≫
                (tensorPullback q).mapIso (θ j) ≪≫ η j) := by
  intro T C _ _ _ _ _ _ 𝒞 _ γ χ hγχ h𝒞 q p hq hpchart η ζ hη hζ hp j
  subst p
  have hψ := irrelevant_le_of_span ψ hgraded
  have hχ := irrelevant_le_of_span χ h𝒞
  have hr := eq_map_of_charts ψ hψ r hchart
  have hq' := eq_map_of_charts χ hχ q hq
  have hrpre (b : A) : r ⁻¹ᵁ basicOpen 𝒜 b = basicOpen ℬ (ψ b) := by
    rw [hr]
    exact Proj.map_preimage_basicOpen ψ hψ b
  have hqpre (b : B) : q ⁻¹ᵁ basicOpen ℬ b = basicOpen 𝒞 (χ b) := by
    rw [hq']
    exact Proj.map_preimage_basicOpen χ hχ b
  simp only [eqToIso_refl, Iso.refl_trans]
  apply Iso.ext
  apply twist_pullback_hom_ext (q ≫ r) j
  intro i k a b ha hb hik U hU s hs
  change (ζ j).hom.app ((q ≫ r) ⁻¹ᵁ U)
    (tensorPullbackSection (q ≫ r) (twist 𝒜 j) U s) =
      (η j).hom.app ((q ≫ r) ⁻¹ᵁ U)
        (((tensorPullback q).map (θ j).hom).app ((q ≫ r) ⁻¹ᵁ U)
          (((tensorPullbackSectionComp q r).hom.app (twist 𝒜 j)).app ((q ≫ r) ⁻¹ᵁ U)
            (tensorPullbackSection (q ≫ r) (twist 𝒜 j) U s)))
  rw [section_comp]
  change scalarExtensionTwistSection (q ≫ r) ζ j U s =
    (η j).hom.app (q ⁻¹ᵁ r ⁻¹ᵁ U)
      (((tensorPullback q).map (θ j).hom).app (q ⁻¹ᵁ r ⁻¹ᵁ U)
        (tensorPullbackSection q ((tensorPullback r).obj (twist 𝒜 j)) (r ⁻¹ᵁ U)
          (tensorPullbackSection r (twist 𝒜 j) U s)))
  rw [section_naturality]
  change scalarExtensionTwistSection (q ≫ r) ζ j U s =
    scalarExtensionTwistSection q η j (r ⁻¹ᵁ U) (scalarExtensionTwistSection r θ j U s)
  apply Subtype.ext
  funext x
  apply Subtype.ext
  have ht : ∀ y : r ⁻¹ᵁ U,
      ((scalarExtensionTwistSection r θ j U s).1 y :
        Localization.AtPrime y.1.asHomogeneousIdeal.toIdeal) * Localization.mk (ψ b) 1 =
          Localization.mk (ψ a) 1 := by
    intro y
    simpa using hθ j i k a b ha hb hik U hU s hs 1 y
  have hV : r ⁻¹ᵁ U ≤ basicOpen ℬ (ψ b) := by
    rw [← hrpre]
    exact r.preimage_mono hU
  have hz := hζ j i k a b ha hb hik U hU s hs 1 x
  have he := hη j i k (ψ a) (ψ b) (ψ.map_mem ha) (ψ.map_mem hb) hik
    (r ⁻¹ᵁ U) hV (scalarExtensionTwistSection r θ j U s) ht 1 x
  have hxden : χ (ψ b) ∉ x.1.asHomogeneousIdeal.toIdeal := by
    have hx : x.1 ∈ (q ≫ r) ⁻¹ᵁ basicOpen 𝒜 b :=
      (q ≫ r).preimage_mono hU x.2
    rwa [Scheme.Hom.comp_preimage, hrpre, hqpre] at hx
  apply (IsLocalization.map_units (Localization.AtPrime x.1.asHomogeneousIdeal.toIdeal)
    (⟨χ (ψ b), hxden⟩ : x.1.asHomogeneousIdeal.toIdeal.primeCompl)).mul_right_cancel
  simpa only [Localization.mk_one_eq_algebraMap, one_smul,
    Proj.one_apply, HomogeneousLocalization.val_one, one_mul,
    GradedRingHom.comp_apply] using hz.trans he.symm

end AlgebraicGeometry.Proj
