import Langlands.Representation.MatrixCoefficient.SquareIntegrableCoefficientCriterionStatement
import Langlands.Representation.MatrixCoefficient.NormRegularityProof
import Langlands.Representation.Category.Contragredient
import Langlands.Representation.OrbitSpan
import Langlands.Topology.LocallyProfiniteProof
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul

/-! # One square-integrable coefficient suffices -/

noncomputable section

universe u v

open MeasureTheory

namespace Langlands.Renard.CompactRepresentation

section IntegrableSubspaces

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace (G ⧸ Subgroup.center G)] [BorelSpace (G ⧸ Subgroup.center G)]
  {V : Type v} [AddCommGroup V] [Module ℂ V]
  {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) (c : UnitaryCentralCharacter ρ)
  (μ : Measure (G ⧸ Subgroup.center G))

/-- Vectors whose coefficient for a fixed functional is square-integrable. -/
private def integrableVectors (ℓ : Module.Dual ℂ V) : Submodule ℂ V where
  carrier := {x | MemLp (c.coefficientNorm ℓ x) 2 μ}
  zero_mem' := by
    have hz : c.coefficientNorm ℓ 0 = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    change MemLp _ 2 μ
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro x y hx hy
    refine (hx.add hy).mono' (c.aestronglyMeasurable_coefficientNorm ℓ (x + y)
      (hρ (x + y)) μ) ?_
    filter_upwards with q
    rw [Real.norm_of_nonneg (c.coefficientNorm_nonneg ℓ (x + y) q)]
    induction q using Quotient.inductionOn with
    | h g =>
      change ‖ℓ (ρ g (x + y))‖ ≤ ‖ℓ (ρ g x)‖ + ‖ℓ (ρ g y)‖
      simpa only [map_add] using norm_add_le (ℓ (ρ g x)) (ℓ (ρ g y))
  smul_mem' := by
    intro a x hx
    have hs : c.coefficientNorm ℓ (a • x) = ‖a‖ • c.coefficientNorm ℓ x := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    change MemLp _ 2 μ
    rw [hs]
    exact hx.const_smul ‖a‖

/-- Smooth functionals whose coefficients for every vector are square-integrable. -/
private def integrableFunctionals : Submodule ℂ (SmoothDual ρ) where
  carrier := {ℓ | ∀ x, MemLp (c.coefficientNorm ℓ.val x) 2 μ}
  zero_mem' := by
    intro x
    have hz : c.coefficientNorm (0 : SmoothDual ρ).val x = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    change MemLp _ 2 μ
    rw [hz]
    exact MemLp.zero
  add_mem' := by
    intro ℓ m hℓ hm x
    refine ((hℓ x).add (hm x)).mono'
      (c.aestronglyMeasurable_coefficientNorm (ℓ + m).val x (hρ x) μ) ?_
    filter_upwards with q
    rw [Real.norm_of_nonneg (c.coefficientNorm_nonneg (ℓ + m).val x q)]
    induction q using Quotient.inductionOn with
    | h g =>
      change ‖ℓ.val (ρ g x) + m.val (ρ g x)‖ ≤ ‖ℓ.val (ρ g x)‖ + ‖m.val (ρ g x)‖
      exact norm_add_le _ _
  smul_mem' := by
    intro a ℓ hℓ x
    have hs : c.coefficientNorm (a • ℓ).val x = ‖a‖ • c.coefficientNorm ℓ.val x := by
      funext q
      induction q using Quotient.inductionOn with
      | h g => simp [matrixCoefficient]
    rw [hs]
    exact (hℓ x).const_smul ‖a‖

private theorem memLp_coefficientNorm_action [μ.IsMulRightInvariant]
    (ℓ : Module.Dual ℂ V) (x : V) (hx : MemLp (c.coefficientNorm ℓ x) 2 μ) (g : G) :
    MemLp (c.coefficientNorm ℓ (ρ g x)) 2 μ := by
  have hp : MeasurePreserving
      (fun q : G ⧸ Subgroup.center G => q * QuotientGroup.mk g) μ μ :=
    ⟨(continuous_id.mul_const _).measurable, map_mul_right_eq_self μ _⟩
  have heq : c.coefficientNorm ℓ (ρ g x) =
      c.coefficientNorm ℓ x ∘ (fun q => q * QuotientGroup.mk g) := by
    funext q
    induction q using Quotient.inductionOn with
    | h k =>
      change ‖ℓ (ρ k (ρ g x))‖ = ‖ℓ (ρ (k * g) x)‖
      rw [map_mul, Module.End.mul_apply]
  rw [heq]
  exact hx.comp_measurePreserving hp

private theorem memLp_coefficientNorm_dual_action [μ.IsMulLeftInvariant]
    (ℓ : SmoothDual ρ) (x : V) (hx : MemLp (c.coefficientNorm ℓ.val x) 2 μ) (g : G) :
    MemLp (c.coefficientNorm (smoothContragredient ρ g ℓ).val x) 2 μ := by
  have hp : MeasurePreserving
      (fun q : G ⧸ Subgroup.center G => QuotientGroup.mk g⁻¹ * q) μ μ :=
    ⟨(continuous_const_mul (QuotientGroup.mk g⁻¹ : G ⧸ Subgroup.center G)).measurable,
      map_mul_left_eq_self μ _⟩
  have heq : c.coefficientNorm (smoothContragredient ρ g ℓ).val x =
      c.coefficientNorm ℓ.val x ∘ (fun q => QuotientGroup.mk g⁻¹ * q) := by
    funext q
    induction q using Quotient.inductionOn with
    | h k =>
      change ‖ℓ.val (ρ g⁻¹ (ρ k x))‖ = ‖ℓ.val (ρ (g⁻¹ * k) x)‖
      rw [map_mul, Module.End.mul_apply]
  rw [heq]
  exact hx.comp_measurePreserving hp

end IntegrableSubspaces

/-- Renard IV.3.2, Remark, with the published admissibility convention. -/
theorem squareIntegrableCoefficientCriterion :
    SquareIntegrableCoefficientCriterionStatement.{u, v} := by
  intro G _ _ _ _ _ _ _ _ μ _ _ π hirr hadm c hex
  obtain ⟨ℓ, x, hnonzero, hL2⟩ := hex
  have hx : x ≠ 0 := by
    intro hx
    apply hnonzero
    rw [hx, map_zero]
  have hℓ : ℓ ≠ 0 := by
    intro hℓ
    apply hnonzero
    rw [hℓ]
    change matrixCoefficient π.representation 0 x = 0
    simp
  have hallx : ∀ y : π, MemLp (c.coefficientNorm ℓ.val y) 2 μ := by
    have hspan : Submodule.span ℂ (Set.range fun g : G => π.representation g x) ≤
        integrableVectors π.isSmooth c μ ℓ.val := by
      apply Submodule.span_le.mpr
      rintro _ ⟨g, rfl⟩
      exact memLp_coefficientNorm_action c μ ℓ.val x hL2 g
    rw [span_range_orbit_eq_top hirr hx] at hspan
    intro y
    exact hspan (Submodule.mem_top)
  have hcofinal : CompactOpenCofinal G := by
    intro K
    obtain ⟨L, hLc, hLK⟩ :=
      ((Topology.LocallyProfiniteProof.vanDantzig G).mp
        Topology.isLocallyProfinite_of_mathlib).2 (K : Set G) K.mem_nhds_one
    exact ⟨L, hLc, hLK⟩
  have hdual : Representation.IsIrreducible (smoothContragredient π.representation) :=
    (π.isIrreducible_contragredient_iff hcofinal hadm).mpr hirr
  have hspan : Submodule.span ℂ (Set.range fun g : G =>
      smoothContragredient π.representation g ℓ) ≤ integrableFunctionals π.isSmooth c μ := by
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩ y
    exact memLp_coefficientNorm_dual_action c μ ℓ y (hallx y) g
  rw [span_range_orbit_eq_top hdual hℓ] at hspan
  exact ⟨hadm, c, fun m y => hspan (Submodule.mem_top) y⟩

end Langlands.Renard.CompactRepresentation
