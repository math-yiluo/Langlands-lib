import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree

/-! # Two-cocycle obstruction for a central lift -/

universe u v w z

open groupCohomology

namespace Langlands

variable {Γ : Type u} [Group Γ] {A : Type v} [CommGroup A]
  {B : Type w} [Group B] {C : Type z} [Group C]
  [MulDistribMulAction Γ B]

/-- Lifts of the coefficients of a crossed cocycle, with their multiplication defect in
an abelian kernel. -/
structure CentralCocycleLift (i : A →* B) (p : B →* C) (c : Γ → C) where
  value : Γ → B
  project : ∀ σ, p (value σ) = c σ
  defect : Γ × Γ → A
  defect_spec : ∀ σ τ, i (defect (σ, τ)) * value (σ * τ) = value σ * σ • value τ

namespace CentralCocycleLift

variable {i : A →* B} {p : B →* C} {c : Γ → C}

/-- An arbitrary lift of each coefficient has a kernel-valued multiplication defect. -/
theorem nonempty_of_lifts [MulDistribMulAction Γ C] (hp : ∀ (σ : Γ) (b : B), p (σ • b) = σ • p b)
    (hexact : ∀ b, p b = 1 ↔ ∃ a, i a = b)
    (hc : ∀ σ τ, c (σ * τ) = c σ * σ • c τ)
    (b : Γ → B) (hb : ∀ σ, p (b σ) = c σ) : Nonempty (CentralCocycleLift i p c) := by
  have h (q : Γ × Γ) : ∃ a, i a = b q.1 * q.1 • b q.2 * (b (q.1 * q.2))⁻¹ := by
    apply (hexact _).mp
    rw [map_mul, map_mul, map_inv, hp, hb, hb, hb, hc, mul_inv_cancel]
  choose d hd using h
  refine ⟨⟨b, hb, d, fun σ τ => ?_⟩⟩
  rw [hd (σ, τ)]
  exact inv_mul_cancel_right _ _

variable [MulDistribMulAction Γ A] (d : CentralCocycleLift i p c)
  (hcentre : ∀ a b, Commute (i a) b) (hiact : ∀ (σ : Γ) (a : A), i (σ • a) = σ • i a)

include hcentre hiact

/-- The multiplication defect is a multiplicative two-cocycle. -/
theorem defect_isMulCocycle₂ (hi : Function.Injective i) : IsMulCocycle₂ d.defect := by
  intro σ τ υ
  apply hi
  rw [map_mul, map_mul, hiact]
  apply mul_right_cancel (b := d.value ((σ * τ) * υ))
  calc
    _ = (i (d.defect (σ, τ)) * i (d.defect (σ * τ, υ))) * d.value ((σ * τ) * υ) := by
      rw [(hcentre (d.defect (σ * τ, υ)) (i (d.defect (σ, τ)))).eq]
    _ = (d.value σ * σ • d.value τ) * (σ * τ) • d.value υ := by
      rw [mul_assoc, d.defect_spec (σ * τ) υ, ← mul_assoc, d.defect_spec σ τ]
    _ = d.value σ * σ • (d.value τ * τ • d.value υ) := by
      rw [mul_smul, smul_mul', mul_assoc]
    _ = d.value σ * (σ • i (d.defect (τ, υ)) * σ • d.value (τ * υ)) := by
      rw [← d.defect_spec τ υ, smul_mul']
    _ = _ := by
      rw [mul_assoc σ τ υ, mul_assoc, d.defect_spec σ (τ * υ), ← mul_assoc]
      rw [← hiact, (hcentre (σ • d.defect (τ, υ)) (d.value σ)).symm.eq, mul_assoc]

/-- A primitive of the two-cocycle corrects the lifts to a crossed cocycle. -/
theorem exists_cocycle_lift_of_isMulCoboundary₂ (hpi : ∀ a, p (i a) = 1)
    (h : IsMulCoboundary₂ d.defect) :
    ∃ b : Γ → B, (∀ σ, p (b σ) = c σ) ∧ ∀ σ τ, b (σ * τ) = b σ * σ • b τ := by
  obtain ⟨a, ha⟩ := h
  refine ⟨fun σ => (i (a σ))⁻¹ * d.value σ, fun σ => ?_, fun σ τ => ?_⟩
  · rw [map_mul, map_inv, hpi, inv_one, one_mul, d.project]
  · have hcoeff : ((a σ)⁻¹ * (σ • a τ)⁻¹) * d.defect (σ, τ) = (a (σ * τ))⁻¹ := by
      rw [← ha, div_mul_eq_mul_div, div_eq_mul_inv]
      simp only [mul_assoc, inv_mul_cancel_left]
    have hB := congrArg i hcoeff
    rw [map_mul, map_mul, map_inv, map_inv, map_inv, hiact] at hB
    rw [smul_mul', smul_inv', ← mul_assoc, mul_assoc (i (a σ))⁻¹,
      ← hiact, (hcentre (σ • a τ) (d.value σ)).inv_left.symm.eq, hiact]
    rw [← mul_assoc, mul_assoc ((i (a σ))⁻¹ * (σ • i (a τ))⁻¹),
      ← d.defect_spec σ τ, ← mul_assoc, hB]

/-- If a crossed-cocycle lift already exists, every multiplication defect is a coboundary. -/
theorem isMulCoboundary₂_of_cocycle_lift (hi : Function.Injective i)
    (hexact : ∀ b, p b = 1 ↔ ∃ a, i a = b)
    (b : Γ → B) (hb : ∀ σ, p (b σ) = c σ)
    (h : ∀ σ τ, b (σ * τ) = b σ * σ • b τ) : IsMulCoboundary₂ d.defect := by
  have hex (σ : Γ) : ∃ a, i a = d.value σ * (b σ)⁻¹ := by
    apply (hexact _).mp
    rw [map_mul, map_inv, d.project, hb, mul_inv_cancel]
  choose a ha using hex
  have hv (σ : Γ) : d.value σ = i (a σ) * b σ := by
    rw [ha, inv_mul_cancel_right]
  refine ⟨a, fun σ τ => ?_⟩
  have key : i (d.defect (σ, τ)) * i (a (σ * τ)) = i (a σ) * i (σ • a τ) := by
    apply mul_right_cancel (b := b (σ * τ))
    calc
      _ = i (d.defect (σ, τ)) * d.value (σ * τ) := by rw [mul_assoc, ← hv]
      _ = d.value σ * σ • d.value τ := d.defect_spec σ τ
      _ = _ := by
        rw [hv σ, hv τ, smul_mul', ← hiact, mul_assoc, ← mul_assoc (b σ),
          (hcentre _ (b σ)).symm.eq, mul_assoc (i (σ • a τ)), ← mul_assoc, ← h]
  rw [← map_mul, ← map_mul] at key
  have h' := hi key
  rw [div_mul_eq_mul_div, mul_comm (σ • a τ), div_eq_iff_eq_mul]
  exact h'.symm

end CentralCocycleLift
end Langlands
