import Langlands.Analysis.Meromorphic.ImaginaryHolomorphicExtension
import Langlands.Global.ImaginaryAxisLocalDivision

/-! # Regularization of a bounded pairing on the imaginary axis -/

noncomputable section

open Filter Metric Set Topology

set_option autoImplicit false

namespace Langlands.Global.ImaginaryAxis

open Langlands.Analysis.Meromorphic.ImaginaryHyperplane

variable {n : ℕ}

/-- Local denominators at points of the imaginary axis. Each vanishing factor is represented
by a real linear form centered at that point, with repetitions allowed. The numerator agrees
with the cleared function wherever the latter is defined on the open set `D`. -/
def HasImaginaryHyperplanePresentation (f : (Fin n → ℂ) → ℂ) (D : Set (Fin n → ℂ)) : Prop :=
  ∀ s₀ ∈ Set.range (imaginarySlice (n := n)), ∃ (m : ℕ)
    (ℓ : Fin m → (Fin n → ℂ) →ₗ[ℂ] ℂ) (W : Set (Fin n → ℂ))
    (h : (Fin n → ℂ) → ℂ),
    (∀ k (x : Fin n → ℝ), (ℓ k (fun j => (x j : ℂ))).im = 0) ∧
    (∀ k, ∃ x : Fin n → ℝ, ℓ k (fun j => (x j : ℂ)) ≠ 0) ∧
    IsOpen W ∧ s₀ ∈ W ∧ DifferentiableOn ℂ h W ∧
    EqOn h (fun s => (∏ k, ℓ k (s - s₀)) * f s) (W ∩ D)

/-- A point on the coordinate imaginary axis is recovered from its imaginary parts. -/
private theorem imaginarySlice_im {s : Fin n → ℂ} (hs : ∀ j, (s j).re = 0) :
    imaginarySlice (fun j => (s j).im) = s := by
  funext j
  apply Complex.ext <;> simp [imaginarySlice, hs j, Complex.mul_re, Complex.mul_im]

/-- Holomorphic extension from bounds on the generic imaginary parameters, as used at the
end of the proof of Delorme's Theorem 7.1. The regular value is the limit along `D`. -/
theorem range_imaginarySlice_subset_extensionDomain_of_locally_bounded
    {f : (Fin n → ℂ) → ℂ} {D : Set (Fin n → ℂ)} (hD : IsOpen D)
    (hcont : ContinuousOn f D) (hDense : Dense (imaginarySlice ⁻¹' D))
    (hp : HasImaginaryHyperplanePresentation f D)
    (hb : ∀ s₀ ∈ Set.range (imaginarySlice (n := n)), ∃ V : Set (Fin n → ℂ),
      IsOpen V ∧ s₀ ∈ V ∧ ∃ B : ℝ, ∀ x : Fin n → ℝ, imaginarySlice x ∈ V ∩ D →
        ‖f (imaginarySlice x)‖ ≤ B) :
    Set.range (imaginarySlice (n := n)) ⊆ extensionDomain f D := by
  classical
  intro s₀ hs₀
  obtain ⟨m, ℓ, W, h, hreal, hne, hW, hsW, hhol, hnum⟩ := hp s₀ hs₀
  obtain ⟨V, hV, hsV, B, hB⟩ := hb s₀ hs₀
  let L : (Fin n → ℂ) → ℂ := fun s => ∏ k, ℓ k (s - s₀)
  have hLc : Continuous L := continuous_finsetProd _ fun k _ =>
    (ℓ k).continuous_of_finiteDimensional.comp (continuous_id.sub continuous_const)
  let U := W ∩ V
  have hU : IsOpen U := hW.inter hV
  have hsU : s₀ ∈ U := ⟨hsW, hsV⟩
  have him₀ : ∀ j, (s₀ j).re = 0 := by
    obtain ⟨x, rfl⟩ := hs₀
    simp [imaginarySlice]
  have hbound (s : Fin n → ℂ) (hs : s ∈ U) (him : ∀ j, (s j).re = 0) :
      ‖h s‖ ≤ B * ‖L s‖ := by
    let O := imaginarySlice ⁻¹' U
    have hO : IsOpen O := hU.preimage continuous_imaginarySlice
    let x : Fin n → ℝ := fun j => (s j).im
    have hx : imaginarySlice x = s := imaginarySlice_im him
    have hxO : x ∈ O := by simpa only [O, mem_preimage, hx] using hs
    have hc := hDense.open_subset_closure_inter hO hxO
    have hcH : ContinuousOn (fun y => ‖h (imaginarySlice y)‖) O :=
      hhol.continuousOn.norm.comp continuous_imaginarySlice.continuousOn fun _ hy => hy.1
    have hcL : Continuous (fun y => B * ‖L (imaginarySlice y)‖) :=
      (hLc.comp continuous_imaginarySlice).norm.const_mul B
    rw [← hx]
    refine ContinuousWithinAt.closure_le hc ((hcH x hxO).mono inter_subset_left)
      hcL.continuousWithinAt ?_
    intro y hy
    rw [hnum ⟨hy.1.1, hy.2⟩, norm_mul, mul_comm]
    exact mul_le_mul_of_nonneg_right (hB y ⟨hy.1.2, hy.2⟩) (norm_nonneg _)
  obtain ⟨r, hr, c, hcd, hcleared⟩ :=
    exists_differentiableOn_mul_eq_of_norm_le_on_imaginary ℓ hreal hne him₀ hU hsU
      (hhol.mono inter_subset_left) (fun s hs hs' _ => hbound s hs hs')
  let N := ball s₀ r ∩ U
  have hN : IsOpen N := isOpen_ball.inter hU
  have hD' : Dense {s | L s ≠ 0} := dense_setOf_prod_ne_zero ℓ
    (fun k => by obtain ⟨v, hv⟩ := hne k; exact ⟨_, hv⟩) s₀
  have heq : EqOn c f ((N ∩ D) ∩ {s | L s ≠ 0}) := by
    rintro s ⟨⟨⟨hsr, hsU'⟩, hsD⟩, hsL⟩
    have hh := hcleared s hsr
    rw [hnum ⟨hsU'.1, hsD⟩] at hh
    exact mul_left_cancel₀ hsL hh
  refine ⟨N, hN, ⟨mem_ball_self hr, hsU⟩, c, hcd.mono inter_subset_left, ?_⟩
  exact heq.of_subset_closure
    ((hcd.mono (inter_subset_left : N ⊆ _)).continuousOn.mono inter_subset_left)
    (hcont.mono inter_subset_right) inter_subset_left
    (hD'.open_subset_closure_inter (hN.inter hD))

/-- Local boundedness follows from a bounded generic comparison with a continuous function
on the imaginary slice. The maximal extension gives a single open domain for the slice. -/
theorem exists_holomorphic_extension_of_generic_comparison
    {f : (Fin n → ℂ) → ℂ} {A : (Fin n → ℝ) → ℂ} {D : Set (Fin n → ℂ)}
    (hD : IsOpen D) (hDc : Dense D) (hDhol : DifferentiableOn ℂ f D)
    (hDense : Dense (imaginarySlice ⁻¹' D)) (hp : HasImaginaryHyperplanePresentation f D)
    (hA : Continuous A)
    (hB : ∀ Λ : Set (Fin n → ℝ), Bornology.IsBounded Λ →
      ∃ B : ℝ, ∀ x ∈ Λ ∩ imaginarySlice ⁻¹' D, ‖A x - f (imaginarySlice x)‖ ≤ B) :
    ∃ (ω : (Fin n → ℂ) → ℂ) (U : Set (Fin n → ℂ)),
      IsOpen U ∧ Set.range (imaginarySlice (n := n)) ⊆ U ∧
      DifferentiableOn ℂ ω U ∧ EqOn ω f (U ∩ D) := by
  refine ⟨maximalExtension f D, extensionDomain f D, isOpen_extensionDomain, ?_,
    differentiableOn_maximalExtension hDc, ?_⟩
  · apply range_imaginarySlice_subset_extensionDomain_of_locally_bounded
      hD hDhol.continuousOn hDense hp
    rintro _ ⟨x₀, rfl⟩
    let imCoords : (Fin n → ℂ) → (Fin n → ℝ) := fun s j => (s j).im
    have hIm : Continuous imCoords :=
      continuous_pi fun j => Complex.continuous_im.comp (continuous_apply j)
    have hIx (x : Fin n → ℝ) : imCoords (imaginarySlice x) = x := by
      ext j
      simp [imCoords, imaginarySlice, Complex.mul_im]
    let V := imCoords ⁻¹' ball x₀ 1
    obtain ⟨B, hBound⟩ := hB (closedBall x₀ 1) isBounded_closedBall
    obtain ⟨C, hC⟩ := (isCompact_closedBall x₀ 1).exists_bound_of_continuousOn hA.continuousOn
    refine ⟨V, isOpen_ball.preimage hIm, ?_, C + B, ?_⟩
    · change imCoords (imaginarySlice x₀) ∈ ball x₀ 1
      rw [hIx]
      exact mem_ball_self zero_lt_one
    · intro x hx
      have hxBall : x ∈ closedBall x₀ 1 := by
        have hIxV : imCoords (imaginarySlice x) ∈ ball x₀ 1 := hx.1
        rw [hIx] at hIxV
        exact ball_subset_closedBall hIxV
      have heq : f (imaginarySlice x) = A x - (A x - f (imaginarySlice x)) := by abel
      calc
        ‖f (imaginarySlice x)‖ = ‖A x - (A x - f (imaginarySlice x))‖ := congrArg norm heq
        _ ≤ ‖A x‖ + ‖A x - f (imaginarySlice x)‖ := norm_sub_le _ _
        _ ≤ C + B := add_le_add (hC x hxBall) (hBound x ⟨hxBall, hx.2⟩)
  · intro s hs
    exact maximalExtension_eqOn hDc hD hDhol (fun _ _ => rfl) hs.2

/-- Extend the comparison estimate to every bounded set of imaginary parameters. The generic
estimate is applied on a slightly larger open ball so that even a set contained in an
exceptional hyperplane inherits the bound. -/
theorem norm_sub_le_of_dense_imaginary
    {f ω : (Fin n → ℂ) → ℂ} {A : (Fin n → ℝ) → ℂ} {D U : Set (Fin n → ℂ)}
    {Λ : Set (Fin n → ℝ)} {r B : ℝ}
    (hDense : Dense (imaginarySlice ⁻¹' D)) (hU : Set.range (imaginarySlice (n := n)) ⊆ U)
    (hω : ContinuousOn ω U) (hEq : EqOn ω f (U ∩ D)) (hA : Continuous A)
    (hΛ : Λ ⊆ ball 0 r)
    (hB : ∀ x ∈ ball (0 : Fin n → ℝ) r ∩ imaginarySlice ⁻¹' D,
      ‖A x - f (imaginarySlice x)‖ ≤ B) :
    ∀ x ∈ Λ, ‖A x - ω (imaginarySlice x)‖ ≤ B := by
  intro x hx
  have hc := hDense.open_subset_closure_inter isOpen_ball (hΛ hx)
  have hcont : Continuous (fun y => ‖A y - ω (imaginarySlice y)‖) := by
    apply Continuous.norm
    exact hA.sub (continuousOn_univ.mp (hω.comp continuous_imaginarySlice.continuousOn
      fun y _ => hU (mem_range_self y)))
  refine ContinuousWithinAt.closure_le hc hcont.continuousWithinAt continuousWithinAt_const ?_
  intro y hy
  rw [hEq ⟨hU (mem_range_self y), hy.2⟩]
  exact hB y hy

end Langlands.Global.ImaginaryAxis
