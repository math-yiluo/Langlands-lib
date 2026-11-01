import Langlands.AbelianScheme.Tate.TwoPowerTorsionClosureSubgroupProof
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # Multiplication on a smooth closed realization of the actual torsion closure -/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

universe u

namespace Langlands.AbelianScheme.Tate

private lemma exists_factor_closedImmersion_of_reduced
    {X Y Z : Scheme.{u}} [IsReduced X]
    (i : Y ⟶ Z) [IsClosedImmersion i] (g : X ⟶ Z)
    (h : Set.range g ⊆ Set.range i) :
    ∃ l : X ⟶ Y, l ≫ i = g := by
  have : Surjective (pullback.snd i g) := ⟨fun x ↦ by
    obtain ⟨y, hy⟩ := h ⟨x, rfl⟩
    obtain ⟨w, -, hw⟩ := Scheme.Pullback.exists_preimage_pullback y x hy
    exact ⟨w, hw⟩⟩
  have := isIso_of_isClosedImmersion_of_surjective (pullback.snd i g)
  refine ⟨inv (pullback.snd i g) ≫ pullback.fst i g, ?_⟩
  rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

variable {K : Type u} [Field K] [IsAlgClosed K]
  (A : AbelianScheme (Spec (CommRingCat.of K)))

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
lemma exists_mul_on_smooth_twoPowerTorsionClosure
    (Y : Scheme.{u}) (i : Y ⟶ A.X.left) [IsClosedImmersion i]
    [Smooth (i ≫ A.X.hom)]
    (hi : Set.range i = closure (twoPowerTorsionLocus A)) :
    let P := Over.mk (i ≫ A.X.hom)
    let j : P ⟶ A.X := Over.homMk i
    ∃ m : P ⊗ P ⟶ P, m ≫ j = (j ⊗ₘ j) ≫ μ[A.X] := by
  let P := Over.mk (i ≫ A.X.hom)
  let j : P ⟶ A.X := Over.homMk i
  let g : P ⊗ P ⟶ A.X := (j ⊗ₘ j) ≫ μ[A.X]
  have : Smooth P.hom := ‹Smooth (i ≫ A.X.hom)›
  have hp : Smooth (P ⊗ P).hom := inferInstanceAs
    (Smooth (pullback.fst P.hom P.hom ≫ P.hom))
  have : IsReduced (P ⊗ P).left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      K (P ⊗ P).left (P ⊗ P).hom
  have : JacobsonSpace (P ⊗ P).left :=
    LocallyOfFiniteType.jacobsonSpace (P ⊗ P).hom
  have hc : IsClosed (g.left ⁻¹' Set.range i) :=
    i.isClosedEmbedding.isClosed_range.preimage g.left.continuous
  have hclosed : closedPoints (P ⊗ P).left ⊆ g.left ⁻¹' Set.range i := by
    intro z hz
    let s : Over.mk (𝟙 (Spec (CommRingCat.of K))) ⟶ P ⊗ P :=
      Over.homMk (pointOfClosedPoint (P ⊗ P).hom z hz)
        (pointOfClosedPoint_comp (P ⊗ P).hom z hz)
    let s₁ := s ≫ fst P P ≫ j
    let s₂ := s ≫ snd P P ≫ j
    have hs₁ : s₁ ∈ twoPowerTorsionClosureSectionSubgroup A := by
      change s₁.left (default : Spec (CommRingCat.of K)) ∈
        closure (twoPowerTorsionLocus A)
      rw [← hi]
      exact ⟨(s ≫ fst P P).left (default : Spec (CommRingCat.of K)), rfl⟩
    have hs₂ : s₂ ∈ twoPowerTorsionClosureSectionSubgroup A := by
      change s₂.left (default : Spec (CommRingCat.of K)) ∈
        closure (twoPowerTorsionLocus A)
      rw [← hi]
      exact ⟨(s ≫ snd P P).left (default : Spec (CommRingCat.of K)), rfl⟩
    have hsg : s ≫ g = s₁ * s₂ := by
      simp only [g, s₁, s₂, Hom.mul_def, ← comp_lift_assoc, lift_fst_comp_snd_comp]
    have hmul := (twoPowerTorsionClosureSectionSubgroup A).mul_mem hs₁ hs₂
    change (s₁ * s₂).left (default : Spec (CommRingCat.of K)) ∈
      closure (twoPowerTorsionLocus A) at hmul
    rw [← hsg, Over.comp_left, Scheme.Hom.comp_apply] at hmul
    change g.left z ∈ Set.range i
    rw [hi]
    simpa [s] using hmul
  have hrange : Set.range g.left ⊆ Set.range i := by
    rintro _ ⟨z, rfl⟩
    have hall : Set.univ ⊆ g.left ⁻¹' Set.range i := by
      rw [← closure_closedPoints]
      exact hc.closure_subset_iff.mpr hclosed
    exact hall (Set.mem_univ z)
  obtain ⟨m, hm⟩ := exists_factor_closedImmersion_of_reduced i g.left hrange
  have hmp : m ≫ P.hom = (P ⊗ P).hom := by
    change m ≫ i ≫ A.X.hom = _
    rw [← Category.assoc, hm, Over.w]
  exact ⟨Over.homMk m hmp, Over.OverMorphism.ext hm⟩

end Langlands.AbelianScheme.Tate
