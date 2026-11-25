/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import WeilConjectures.AlgebraicGeometry.RelativeProj.GradedTensor

/-!
# Scalar extension of affine Proj with its chart maps

Source: literature/stacks-project/constructions.tex, Tags 01N2 and 01MY
(blueprint: lem-nagata-affine-proj-scalar-extension)
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry

namespace AlgebraicGeometry

/-- Scalar extension of affine Proj, with the standard-open descriptions.
Source: Stacks Project, Tags 01N2 and 01MY (blueprint: lem-nagata-affine-proj-scalar-extension).
Proof: the graded scalar-extension condition expresses every positive-degree element of B
as a finite S-linear combination of images of homogeneous elements of A. These images generate
the irrelevant ideal, so their standard opens cover (definition-admissible-blow-up--1). On each such
open, lem-nagata-homogeneous-localization-scalar-extension and
lem-weil-pbc-fibre-product-affine-spectra identify the chart with the affine fibre product.
The projection is induced by Away.map, whose fraction formula is Away.map_mk.
On intersections, lem-weil-pbc-proj-basic-open-intersection and
lemma-nagata-proj-chart-ring-cocycle identify both projections with the same fraction map.
Then lem-weil-pbc-scheme-morphism-gluing glues them and proves the inverse-image formula.
For any test scheme with compatible maps to Proj A and Spec S, restrict to these opens,
use chartwise pullback uniqueness, and glue the lifts; this proves the cartesian square
(def-pc-fibre-product). Finally, maps with the stated chart formulas agree on the cover,
so gluing uniqueness proves the final clause. No cancellation or flatness is used.
-/
theorem lem_nagata_affine_proj_scalar_extension
    {R : Type u} [CommRing R] {S : Type u} [CommRing S]
    {A : Type u} [CommRing A] {B : Type u} [CommRing B]
    [Algebra R S] [Algebra R A] [Algebra S B]
    (𝒜 : ℕ → Submodule R A) (ℬ : ℕ → Submodule S B)
    [GradedRing 𝒜] [GradedRing ℬ]
    (ρA : R →+* 𝒜 0) (ρB : S →+* ℬ 0)
    (hρA : ∀ r : R, (ρA r : A) = algebraMap R A r)
    (hρB : ∀ s : S, (ρB s : B) = algebraMap S B s)
    (β : TensorProduct R S A ≃ₐ[S] B)
    (ψ : 𝒜 →+*ᵍ ℬ)
    (hβψ : ∀ a : A, β (TensorProduct.tmul R (1 : S) a) = ψ a)
    (hgraded : ∀ n : ℕ, ℬ n = Submodule.span S (ψ '' (𝒜 n : Set A))) :
    ∃ (r : Proj ℬ ⟶ Proj 𝒜),
      CategoryTheory.IsPullback r
        (Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom ρB))
        (Proj.toSpecZero 𝒜 ≫ Spec.map (CommRingCat.ofHom ρA))
        (Spec.map (CommRingCat.ofHom (algebraMap R S))) ∧
      (∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
        r ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (ψ f)) ∧
      (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
        Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r =
          Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
            Proj.awayι 𝒜 f hf hn) ∧
      (⨆ (p : {p : ℕ × A // p.2 ∈ 𝒜 p.1 ∧ 0 < p.1}),
        Proj.basicOpen ℬ (ψ p.1.2)) = ⊤ ∧
      (∀ r' : Proj ℬ ⟶ Proj 𝒜,
        (∀ (n : ℕ) (f : A), f ∈ 𝒜 n → 0 < n →
          r' ⁻¹ᵁ Proj.basicOpen 𝒜 f = Proj.basicOpen ℬ (ψ f)) →
        (∀ (n : ℕ) (f : A) (hf : f ∈ 𝒜 n) (hn : 0 < n),
          Proj.awayι ℬ (ψ f) (ψ.map_mem hf) hn ≫ r' =
            Spec.map (CommRingCat.ofHom (HomogeneousLocalization.Away.map ψ f)) ≫
              Proj.awayι 𝒜 f hf hn) → r' = r) := by
  classical
  have hψ : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map ψ := by
    change (HomogeneousIdeal.irrelevant ℬ).toIdeal ≤ _
    apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
    intro n hn b hb
    rw [hgraded n] at hb
    induction hb using Submodule.span_induction with
    | mem x hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        exact Ideal.mem_map_of_mem ψ
          (HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn ha)
    | zero => exact Ideal.zero_mem _
    | add x y hx hy hx' hy' => exact Ideal.add_mem _ hx' hy'
    | smul s x hx hx' =>
        rw [Algebra.smul_def]
        exact Ideal.mul_mem_left _ _ hx'
  refine ⟨Proj.map ψ hψ, ?_, ?_, ?_, ?_, ?_⟩
  · have hβgrade (n : ℕ) :
        ((𝒜 n).baseChange S).map β.toLinearMap = ℬ n := by
      rw [Submodule.baseChange_eq_span, Submodule.map_span, hgraded n]
      congr 1
      ext b
      simp only [Set.mem_image, SetLike.mem_coe, Submodule.mem_map]
      constructor
      · rintro ⟨x, ⟨a, ha, rfl⟩, rfl⟩
        exact ⟨a, ha, (hβψ a).symm⟩
      · rintro ⟨a, ha, rfl⟩
        exact ⟨TensorProduct.tmul R 1 a, ⟨a, ha, rfl⟩, hβψ a⟩
    let : Algebra R B := Algebra.compHom B (algebraMap R S)
    let : IsScalarTower R S B := IsScalarTower.of_algebraMap_eq' rfl
    have hψR (r : R) : ψ (algebraMap R A r) = algebraMap R B r := by
      rw [← hβψ]
      rw [← Algebra.TensorProduct.tmul_one_eq_one_tmul]
      change β (algebraMap R S r ⊗ₜ[R] (1 : A)) = _
      change β (algebraMap S (TensorProduct R S A) (algebraMap R S r)) = _
      rw [β.commutes]
      rfl
    have hbase : ψ.IsGradedBaseChange := by
      refine ⟨hψR, fun n ↦ ?_⟩
      let e := (LinearEquiv.ofBijective ((𝒜 n).toBaseChange S)
        (DirectSum.toBaseChange_bijective 𝒜 n)).trans
          (β.toLinearEquiv.ofSubmodules _ _ (hβgrade n))
      apply IsBaseChange.of_equiv e
      intro a
      apply Subtype.ext
      exact hβψ a
    have hρA' : ρA = algebraMap R (𝒜 0) := by
      ext r
      exact hρA r
    have hρB' : ρB = algebraMap S (ℬ 0) := by
      ext s
      exact hρB s
    simpa only [Proj.toSpecOfAlgebra, hρA', hρB'] using
      (Proj.isPullback_map_of_isGradedBaseChange ψ hbase)
  · intro n f hf hn
    exact Proj.map_preimage_basicOpen ψ hψ f
  · intro n f hf hn
    exact Proj.awayι_comp_map ψ hψ hn f hf
  · apply top_le_iff.mp
    rw [← Scheme.OpenCover.iSup_opensRange (Proj.mapAffineOpenCover ψ hψ).openCover]
    apply iSup_le
    intro i
    simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f,
      Proj.opensRange_awayι]
    exact le_iSup_of_le ⟨(i.1, i.2), i.2.2, i.1.2⟩ le_rfl
  · intro r'  hpre hchart
    apply (Proj.mapAffineOpenCover ψ hψ).openCover.hom_ext
    intro i
    exact (hchart i.1 i.2 i.2.2 i.1.2).trans
      (Proj.awayι_comp_map ψ hψ i.1.2 i.2 i.2.2).symm

end AlgebraicGeometry
