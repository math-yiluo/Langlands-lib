import Langlands.BaseChange.TwistedLocalDescent.MassReduction
import Langlands.BaseChange.TwistedLocalDescent.MassChartAlgebra

/-! # Restriction of the twisted orbital kernel to `d (P ∩ K(r))`

Support and restriction lemmas for the twisted orbital kernel, with `K(r)` the congruence
subgroup of radius `r` and `A` the linear part of the twisted chart at `d`. Under chart support
(every `y` with `φ(x y θ(x)⁻¹) ≠ 0` is `d (1 + Y)` with `Y ∈ A(B(0, r))` and `‖Y‖ ≤ r`) and
pointwise rigidity (a twisted conjugator from an element of `Q` to an element of `d (P ∩ K(r))`
lies in `P`), the elements `k` with nonzero kernel value lie in `P K(r) x⁻¹`
(`rel_of_twistedOrbitalKernel_ne_zero`). If moreover the weight `δh` is multiplicative and
trivial on `P ∩ K(r)` and `d (P ∩ K(r)) ⊆ Q`, then on the opposite unipotent coordinates the
integral over `Q` restricts to `d (P ∩ K(r))` (`twistedOrbitalKernel_lowerUnit_mul_inv`). The
full mass calculation, with its additional hypotheses, is `integral_twistedOrbitalKernel_eq_mass`
in `Langlands.BaseChange.TwistedLocalDescent.MassIdentity`. See the paired Markdown.
-/

noncomputable section

namespace Langlands.BaseChange.TwistedLocalDescent

open MeasureTheory Measure Set Metric Topology
open Langlands.GeneralLinear
open scoped ENNReal NNReal

universe v

section Extension

variable {α β : Type*}

/-- Extension by zero along an open embedding preserves continuity of compactly supported
functions. -/
theorem continuous_extend_zero_of_isOpenEmbedding [TopologicalSpace α] [TopologicalSpace β]
    [T2Space β] {e : α → β} (he : IsOpenEmbedding e)
    {f : α → ℂ} (hf : Continuous f) (hs : HasCompactSupport f) :
    Continuous (Function.extend e f 0) := by
  refine continuous_of_tsupport fun y hy => ?_
  have hsub : tsupport (Function.extend e f 0) ⊆ e '' tsupport f :=
    hs.tsupport_extend_zero_subset he.continuous
  obtain ⟨a, -, rfl⟩ := hsub hy
  rw [← he.continuousAt_iff, Function.extend_comp he.injective]
  exact hf.continuousAt

theorem extend_zero_apply_of_injective {e : α → β} (he : Function.Injective e) (f : α → ℂ)
    (a : α) : Function.extend e f 0 (e a) = f a :=
  he.extend_apply f 0 a

theorem exists_eq_of_extend_zero_ne {e : α → β} (he : Function.Injective e) {f : α → ℂ} {y : β}
    (h : Function.extend e f 0 y ≠ 0) : ∃ a, e a = y ∧ f a ≠ 0 := by
  by_cases hy : ∃ a, e a = y
  · obtain ⟨a, rfl⟩ := hy
    exact ⟨a, rfl, by rwa [he.extend_apply] at h⟩
  · exact absurd (Function.extend_apply' f (0 : β → ℂ) y hy) h

end Extension

section Mass

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace matrix_isUltrametricDist
  matrixSupNormedRing matrixSupNormedAlgebra matrix_properSpace matrix_locallyCompactSpace
  parabolicSubalgebra_locallyCompact parabolicSubalgebra_isTopologicalRing
  lowerLie_locallyCompact matrix_secondCountable lowerLie_secondCountable
  parabolicSubalgebra_secondCountable

variable {𝕂 : Type v} [NontriviallyNormedField 𝕂] [IsUltrametricDist 𝕂] [ProperSpace 𝕂]
  {n : ℕ} (B : BlockShape n) (σ : 𝕂 →+* 𝕂)

/-- Points of the support of `φ(x · θ(x)⁻¹)` are twisted conjugates of `d (P ∩ K(r))` by `Ū`. -/
theorem exists_twistedConj_of_support (d : GeneralLinear n 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) {r : ℝ}
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (himg : twistedChart B σ d.val (d⁻¹).val '' closedBall 0 r = A '' closedBall 0 r)
    (φx : GeneralLinear n 𝕂 → ℂ)
    (hsupp : ∀ y, φx y ≠ 0 → ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧
      y.val = d.val * (1 + Y))
    {y : GeneralLinear n 𝕂} (hy : φx y ≠ 0) :
    ∃ Z : lowerLie (E := 𝕂) B, ‖(Z : Matrix (Fin n) (Fin n) 𝕂)‖ ≤ r ∧
      ∃ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U ∧
        y = (lowerUnit B Z)⁻¹ * d * h * Matrix.GeneralLinearGroup.map σ (lowerUnit B Z) := by
  obtain ⟨Y, hYA, -, hyY⟩ := hsupp y hy
  rw [← himg] at hYA
  obtain ⟨X, hX, rfl⟩ := hYA
  exact exists_twistedConj_of_mem_chart B σ d U hrange (mem_closedBall_zero_iff.mp hX) hyY

theorem lowerUnit_mem_congruence (U : OpenSubgroup (GeneralLinear n 𝕂)) {r : ℝ}
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (Z : lowerLie (E := 𝕂) B) (hZ : ‖(Z : Matrix (Fin n) (Fin n) 𝕂)‖ ≤ r) :
    lowerUnit B Z ∈ U := by
  change lowerUnit B Z ∈ (U : Set (GeneralLinear n 𝕂))
  rw [hU]
  change (1 + (Z : Matrix (Fin n) (Fin n) 𝕂)) - 1 ∈ closedBall 0 r
  rwa [add_sub_cancel_left, mem_closedBall_zero_iff]

variable [MeasurableSpace (GeneralLinear n 𝕂)] [BorelSpace (GeneralLinear n 𝕂)]

omit [BorelSpace (GeneralLinear n 𝕂)] in
/-- **The support relation needed for the β-identity.** -/
theorem rel_of_twistedOrbitalKernel_ne_zero (d : B.parabolic 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) {r : ℝ}
    (hU : (U : Set (GeneralLinear n 𝕂)) =
      {g | g.val - 1 ∈ closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r})
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (himg : twistedChart B σ (d : GeneralLinear n 𝕂).val ((d : GeneralLinear n 𝕂)⁻¹).val ''
      closedBall 0 r = A '' closedBall 0 r)
    (μP : Measure (B.parabolic 𝕂)) (Q : Set (B.parabolic 𝕂)) (δh : B.parabolic 𝕂 → ℝ)
    (φ : GeneralLinear n 𝕂 → ℂ) (x : GeneralLinear n 𝕂)
    (hsupp : ∀ y : GeneralLinear n 𝕂,
      φ (x * y * (Matrix.GeneralLinearGroup.map σ x)⁻¹) ≠ 0 →
        ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧
          y.val = (d : GeneralLinear n 𝕂).val * (1 + Y))
    (hrig : ∀ (g : GeneralLinear n 𝕂) (p h : B.parabolic 𝕂), p ∈ Q →
      (h : GeneralLinear n 𝕂) ∈ U →
      g * p * (Matrix.GeneralLinearGroup.map σ g)⁻¹ = d * h → g ∈ B.parabolic 𝕂)
    (k : GeneralLinear n 𝕂)
    (hk : twistedOrbitalKernel (Matrix.GeneralLinearGroup.map σ) μP Q δh φ k ≠ 0) :
    ∃ h : B.parabolic 𝕂, ∃ w ∈ U.toSubgroup, k = h * w * x⁻¹ := by
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) σ
  obtain ⟨p, hp⟩ : ∃ p : B.parabolic 𝕂,
      Q.indicator (fun p : B.parabolic 𝕂 => (δh p : ℂ) * φ (k⁻¹ * p * θ k)) p ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hk
    unfold twistedOrbitalKernel
    rw [integral_congr_ae (Filter.Eventually.of_forall hcon), integral_zero]
  have hpQ : p ∈ Q := by
    by_contra h'
    exact hp (Set.indicator_of_notMem h' _)
  rw [Set.indicator_of_mem hpQ] at hp
  have hφ : φ (k⁻¹ * p * θ k) ≠ 0 := right_ne_zero_of_mul hp
  set y := x⁻¹ * k⁻¹ * p * θ k * θ x
  have hy : φ (x * y * (θ x)⁻¹) ≠ 0 := by
    have : x * y * (θ x)⁻¹ = k⁻¹ * p * θ k := by simp only [y]; group
    rwa [this]
  obtain ⟨Z, hZ, h, hhU, hyeq⟩ := exists_twistedConj_of_support B σ (d : GeneralLinear n 𝕂) U
    hrange A himg (fun y => φ (x * y * (θ x)⁻¹)) hsupp hy
  set u := lowerUnit B Z
  change y = u⁻¹ * d * h * θ u at hyeq
  set g := u * x⁻¹ * k⁻¹
  have hg : g * p * (θ g)⁻¹ = d * h := by
    have h1 : g * p * (θ g)⁻¹ = u * y * (θ u)⁻¹ := by
      simp only [g, y, map_mul, map_inv]
      group
    rw [h1, hyeq]
    group
  have hgP := hrig g p h hpQ hhU hg
  refine ⟨⟨g⁻¹, (B.parabolic 𝕂).inv_mem hgP⟩, u, lowerUnit_mem_congruence B U hU Z hZ, ?_⟩
  simp only [g]
  group

omit [BorelSpace (GeneralLinear n 𝕂)] in
/-- **Restriction to `d (P ∩ K(r))`.** Under chart support and rigidity, with `δh`
multiplicative and trivial on `P ∩ K(r)` and `d (P ∩ K(r)) ⊆ Q`, only `p ∈ d (P ∩ K(r))`
contribute to the twisted orbital kernel on the opposite unipotent ball. -/
theorem twistedOrbitalKernel_lowerUnit_mul_inv [MeasurableSpace (B.parabolic 𝕂)]
    [BorelSpace (B.parabolic 𝕂)] (d : B.parabolic 𝕂)
    (U : OpenSubgroup (GeneralLinear n 𝕂)) {r : ℝ}
    (hrange : Set.range (fun g : U => (g : GeneralLinear n 𝕂).val - 1) =
      closedBall (0 : Matrix (Fin n) (Fin n) 𝕂) r)
    (A : Matrix (Fin n) (Fin n) 𝕂 ≃ₜ+ Matrix (Fin n) (Fin n) 𝕂)
    (himg : twistedChart B σ (d : GeneralLinear n 𝕂).val ((d : GeneralLinear n 𝕂)⁻¹).val ''
      closedBall 0 r = A '' closedBall 0 r)
    (μP : Measure (B.parabolic 𝕂)) [μP.IsMulLeftInvariant] (Q : Set (B.parabolic 𝕂))
    (δh : B.parabolic 𝕂 → ℝ) (hδmul : ∀ a b, δh (a * b) = δh a * δh b)
    (hδW : ∀ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U → δh h = 1)
    (hdQ : ∀ h : B.parabolic 𝕂, (h : GeneralLinear n 𝕂) ∈ U → d * h ∈ Q)
    (φ : GeneralLinear n 𝕂 → ℂ) (x : GeneralLinear n 𝕂)
    (hsupp : ∀ y : GeneralLinear n 𝕂,
      φ (x * y * (Matrix.GeneralLinearGroup.map σ x)⁻¹) ≠ 0 →
        ∃ Y, Y ∈ A '' closedBall 0 r ∧ ‖Y‖ ≤ r ∧
          y.val = (d : GeneralLinear n 𝕂).val * (1 + Y))
    (hrig : ∀ (g : GeneralLinear n 𝕂) (p h : B.parabolic 𝕂), p ∈ Q →
      (h : GeneralLinear n 𝕂) ∈ U →
      g * p * (Matrix.GeneralLinearGroup.map σ g)⁻¹ = d * h → g ∈ B.parabolic 𝕂)
    (Z : lowerLie (E := 𝕂) B) :
    twistedOrbitalKernel (Matrix.GeneralLinearGroup.map σ) μP Q δh φ (lowerUnit B Z * x⁻¹) =
      (δh d : ℂ) * ∫ h, {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ U}.indicator
        (fun h : B.parabolic 𝕂 => φ (x * ((lowerUnit B Z)⁻¹ * d * h *
          Matrix.GeneralLinearGroup.map σ (lowerUnit B Z)) *
            (Matrix.GeneralLinearGroup.map σ x)⁻¹)) h ∂μP := by
  set θ := Matrix.GeneralLinearGroup.map (n := Fin n) σ
  set u := lowerUnit B Z
  set H := {h : B.parabolic 𝕂 | (h : GeneralLinear n 𝕂) ∈ U}
  set G : B.parabolic 𝕂 → ℂ := H.indicator (fun h : B.parabolic 𝕂 =>
    (δh d : ℂ) * φ (x * (u⁻¹ * d * h * θ u) * (θ x)⁻¹))
  have hRHS : (δh d : ℂ) * ∫ h, H.indicator (fun h : B.parabolic 𝕂 =>
      φ (x * (u⁻¹ * d * h * θ u) * (θ x)⁻¹)) h ∂μP = ∫ p, G (d⁻¹ * p) ∂μP := by
    rw [integral_mul_left_eq_self G d⁻¹, ← integral_const_mul]
    congr 1
    funext h
    by_cases hh : h ∈ H
    · simp only [G, Set.indicator_of_mem hh]
    · simp only [G, Set.indicator_of_notMem hh, mul_zero]
  change _ = (δh d : ℂ) * ∫ h, H.indicator (fun h : B.parabolic 𝕂 =>
      φ (x * (u⁻¹ * d * h * θ u) * (θ x)⁻¹)) h ∂μP
  rw [hRHS]
  unfold twistedOrbitalKernel
  have hsimp : ∀ p : B.parabolic 𝕂, (u * x⁻¹)⁻¹ * (p : GeneralLinear n 𝕂) * θ (u * x⁻¹) =
      x * (u⁻¹ * p * θ u) * (θ x)⁻¹ := by
    intro p
    simp only [map_mul, map_inv]
    group
  simp only [hsimp]
  congr 1
  funext p
  have hcancel : u⁻¹ * (d : GeneralLinear n 𝕂) * ((d : GeneralLinear n 𝕂)⁻¹ * p) =
      u⁻¹ * p := by group
  by_cases hpQ : p ∈ Q
  · rw [Set.indicator_of_mem hpQ]
    by_cases hφ : φ (x * (u⁻¹ * p * θ u) * (θ x)⁻¹) = 0
    · rw [hφ, mul_zero]
      by_cases hH : d⁻¹ * p ∈ H
      · simp only [G, Set.indicator_of_mem hH, Subgroup.coe_mul, Subgroup.coe_inv]
        rw [hcancel, hφ, mul_zero]
      · simp only [G, Set.indicator_of_notMem hH]
    · obtain ⟨Z', hZ', h', hh'U, hyeq⟩ := exists_twistedConj_of_support B σ (d : GeneralLinear n 𝕂)
        U hrange A himg (fun y => φ (x * y * (θ x)⁻¹)) hsupp hφ
      set u' := lowerUnit B Z'
      change u⁻¹ * p * θ u = u'⁻¹ * d * h' * θ u' at hyeq
      have hg : (u' * u⁻¹) * p * (θ (u' * u⁻¹))⁻¹ = d * h' := by
        have : (u' * u⁻¹) * p * (θ (u' * u⁻¹))⁻¹ = u' * (u⁻¹ * p * θ u) * (θ u')⁻¹ := by
          simp only [map_mul, map_inv]
          group
        rw [this, hyeq]
        group
      have hgP := hrig (u' * u⁻¹) p h' hpQ hh'U hg
      have hZZ : Z' = Z := lowerUnit_eq_of_mul_inv_mem B Z Z' hgP
      have hpd : p = d * h' := by
        apply Subtype.ext
        have : (p : GeneralLinear n 𝕂) = u * (u'⁻¹ * d * h' * θ u') * (θ u)⁻¹ := by
          rw [← hyeq]
          group
        rw [this]
        simp only [u', hZZ]
        change u * (u⁻¹ * d * h' * θ u) * (θ u)⁻¹ = (d : GeneralLinear n 𝕂) * h'
        group
      have hH : d⁻¹ * p ∈ H := by
        rw [hpd, inv_mul_cancel_left]
        exact hh'U
      simp only [G, Set.indicator_of_mem hH, Subgroup.coe_mul, Subgroup.coe_inv]
      rw [hcancel]
      congr 1
      rw [hpd, hδmul, hδW h' hh'U, mul_one]
  · rw [Set.indicator_of_notMem hpQ]
    have hH : d⁻¹ * p ∉ H := by
      intro hH
      apply hpQ
      have := hdQ (d⁻¹ * p) hH
      rwa [mul_inv_cancel_left] at this
    simp only [G, Set.indicator_of_notMem hH]

end Mass

end Langlands.BaseChange.TwistedLocalDescent
