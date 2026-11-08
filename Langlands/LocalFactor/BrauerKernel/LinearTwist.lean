import Langlands.LocalFactor.RankOneStationaryPhase

/-! # Twisting by small characters at an arbitrary deep linearization -/

noncomputable section

open MeasureTheory
open scoped WithZero

namespace Langlands.LocalFactor.RankOneStability

universe u
variable {p : ℕ} [Fact p.Prime] {F : PadicField.{u} p} (T : F.TopologicalData)

local notation "Character" => @HarmonicAnalysis.Quasicharacter F.Carrier _ T.topology
local notation "AdditiveCharacter" =>
  @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology
local notation "LocalHaar" =>
  @HarmonicAnalysis.AdditiveHaarMeasure F.Carrier _ T.topology (@borel F.Carrier T.topology)

open PadicAbelian

/-- A deep linearization by a large parameter forces a large conductor. -/
theorem lt_multiplicativeConductor_of_linearization (χ : Character) (ψ : AdditiveCharacter)
    (c : F.Carrierˣ) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hlin : letI := T.topology; ∀ x : T.additiveLattice (-(m₀ : ℤ)),
      (χ (oneAddUnit T hm₀ x) : ℂ) = ψ.complex ((c : F.Carrier) * x.val))
    (j : ℕ) (hj : m₀ ≤ j) (hbig : T.ord (c : F.Carrier) + j < -T.additiveConductor ψ) :
    j < T.multiplicativeConductor χ := by
  let := T.topology
  by_contra hle
  push Not at hle
  obtain ⟨w, hw, hψw⟩ := T.exists_nontrivial_at_conductor_succ ψ
  have hc0 : (c : F.Carrier) ≠ 0 := c.ne_zero
  have hxw : (c : F.Carrier) * ((c : F.Carrier)⁻¹ * w) = w := by
    rw [← mul_assoc, mul_inv_cancel₀ hc0, one_mul]
  have hx : (c : F.Carrier)⁻¹ * w ∈ T.additiveLattice (-(j : ℤ)) := by
    have h := (T.mul_mem_additiveLattice_iff hc0 _ _).mp (hxw.symm ▸ hw)
    exact T.additiveLattice_mono (by omega) h
  have hj0 : 0 < j := lt_of_lt_of_le hm₀ hj
  let x₀ : T.additiveLattice (-(m₀ : ℤ)) :=
    ⟨(c : F.Carrier)⁻¹ * w, T.additiveLattice_mono (by omega) hx⟩
  let x : T.additiveLattice (-(j : ℤ)) := ⟨(c : F.Carrier)⁻¹ * w, hx⟩
  have hsame : oneAddUnit T hm₀ x₀ = oneAddUnit T hj0 x := Units.ext rfl
  have htriv := ((T.multiplicativeTrivialAt_iff_conductor_le χ j).mpr hle) _
    (oneAddUnit_mem T hj0 x)
  have h := hlin x₀
  rw [hsame, htriv, Units.val_one] at h
  have h2 : ψ.complex w = 1 := by
    rw [← hxw]
    exact h.symm
  rw [HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply] at h2
  exact hψw (Circle.coe_eq_one.mp h2)

/-- **Small twists at a deep linearization.** Let `χ(1+x) = ψ(c x)` on the lattice
`p^m₀`, where the parameter is large: `ord c + m₀ + K ≤ -n(ψ)` and
`ord c + 2K ≤ -n(ψ)`. Then twisting by any `η` of conductor at most `K` multiplies
the abelian epsilon expression by `η(c)⁻¹`, for every Haar measure. -/
theorem abelianEpsilonExpression_mul_of_linearization (χ : Character) (ψ : AdditiveCharacter)
    (c : F.Carrierˣ) {m₀ : ℕ} (hm₀ : 0 < m₀)
    (hlin : letI := T.topology; ∀ x : T.additiveLattice (-(m₀ : ℤ)),
      (χ (oneAddUnit T hm₀ x) : ℂ) = ψ.complex ((c : F.Carrier) * x.val))
    (K : ℕ) (hK : 0 < K)
    (hbig₁ : T.ord (c : F.Carrier) + ((m₀ + K : ℕ) : ℤ) ≤ -T.additiveConductor ψ)
    (hbig₂ : T.ord (c : F.Carrier) + ((2 * K : ℕ) : ℤ) ≤ -T.additiveConductor ψ)
    (η : Character) (hη : T.multiplicativeConductor η ≤ K) (μ : LocalHaar) :
    T.abelianEpsilonExpression (χ * η) ψ μ =
      (η c⁻¹ : ℂ) * T.abelianEpsilonExpression χ ψ μ := by
  let := T.topology
  let : MeasurableSpace F.Carrier := borel F.Carrier
  let a := T.multiplicativeConductor χ
  have ha : m₀ + K ≤ a ∧ 2 * K ≤ a := by
    have h := lt_multiplicativeConductor_of_linearization T χ ψ c hm₀ hlin
      (max (m₀ + K) (2 * K) - 1) (by omega) (by
        rcases le_total (m₀ + K) (2 * K) with hle | hle
        · rw [max_eq_right hle]; omega
        · rw [max_eq_left hle]; omega)
    change max (m₀ + K) (2 * K) - 1 < a at h
    omega
  let m := a - K
  have hm : 0 < m := by omega
  have hlevels : a = m + K := by omega
  have hm₀m : m₀ ≤ m := by omega
  have hlin' : ∀ x : T.additiveLattice (-(m : ℤ)),
      (χ (oneAddUnit T hm x) : ℂ) = ψ.complex ((c : F.Carrier) * x.val) := by
    intro x
    have hx : x.val ∈ T.additiveLattice (-(m₀ : ℤ)) := T.additiveLattice_mono (by omega) x.2
    have hsame : oneAddUnit T hm x = oneAddUnit T hm₀ ⟨x.val, hx⟩ := Units.ext rfl
    rw [hsame, hlin]
  have hc0 : (c : F.Carrier) ≠ 0 := c.ne_zero
  have hcmem : (c : F.Carrier) ∈ T.additiveLattice (T.additiveConductor ψ + a) := by
    have h := T.mem_additiveLattice_of_forall_complex_mul_eq_one ψ (-(a : ℤ)) c (by
      intro x hx
      have hxm : x ∈ T.additiveLattice (-(m₀ : ℤ)) := T.additiveLattice_mono (by omega) hx
      have ha0 : 0 < a := by omega
      rw [← hlin ⟨x, hxm⟩]
      have hsame : oneAddUnit T hm₀ ⟨x, hxm⟩ = oneAddUnit T ha0 ⟨x, hx⟩ := Units.ext rfl
      rw [hsame, (T.multiplicativeConductor_spec χ) _ (oneAddUnit_mem T ha0 ⟨x, hx⟩),
        Units.val_one])
    simpa only [sub_neg_eq_add] using h
  have hcnot : (c : F.Carrier) ∉ T.additiveLattice (T.additiveConductor ψ + (a - 1 : ℕ)) := by
    intro hmem
    obtain ⟨v, hv, hχv⟩ := T.exists_nontrivial_below_multiplicativeConductor χ (a - 1)
      (by omega)
    have hx : (v : F.Carrier) - 1 ∈ T.additiveLattice (-((a - 1 : ℕ) : ℤ)) := hv.2
    have hxm : (v : F.Carrier) - 1 ∈ T.additiveLattice (-(m₀ : ℤ)) :=
      T.additiveLattice_mono (by omega) hx
    apply hχv
    apply Units.ext
    have heq : oneAddUnit T hm₀ ⟨(v : F.Carrier) - 1, hxm⟩ = v := by
      apply Units.ext
      simp
    rw [← heq, hlin, Units.val_one]
    apply T.complex_eq_one_of_mem_conductor ψ
    have hh := T.mul_mem_additiveLattice_add hmem hx
    simpa only [add_neg_cancel_right] using hh
  have hord : T.ord (c : F.Carrier) = -(T.additiveConductor ψ + a) := by
    rw [T.mem_additiveLattice, gauss_valuation_le_exp_iff T hc0] at hcmem hcnot
    have : 1 ≤ a := by omega
    push_cast [this] at hcnot
    omega
  have hηm : T.multiplicativeConductor η ≤ m := by omega
  have hint := gauss_integral_twist T χ η ψ μ a m K hm hlevels hη hηm c hord hlin'
  have hcond := (conductor_and_L T χ (by omega) η (by omega)).1
  have ha0 : T.multiplicativeConductor χ ≠ 0 := by omega
  rw [← deligneConstant_eq_abelianEpsilonExpression, ← deligneConstant_eq_abelianEpsilonExpression]
  dsimp only [deligneConstant, epsilon]
  rw [hcond]
  simp only [epsilonAt, ha0, ↓reduceIte]
  exact hint

end Langlands.LocalFactor.RankOneStability
