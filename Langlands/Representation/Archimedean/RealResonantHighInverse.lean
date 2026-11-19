import Langlands.Representation.Archimedean.RealGenericMultiplierDegeneration

/-! # Analytic inverse of a resonant tail on its high Fourier modes -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Archimedean.RealResonantHighInverse

open RealBlockMultiplier RealGenericMultiplierDegeneration

variable {ε : ℤ} {r ℓ : ℕ}

/-- The erased-denominator multiplier translated so its removable pole is at zero. -/
def shiftedTail (ε : ℤ) (r : ℕ) (z : ℂ) : ℤ → ℂ :=
  regularizedMultiplier (-((ε : ℂ) + 2 * r + 1) + z) ε r

/-- The scalar normalizing the erased product at the first nonzero mode. -/
def residue (ε : ℤ) (r : ℕ) : ℂ :=
  regularizedSeq (-((ε : ℂ) + 2 * r + 1)) ε r (r + 1)

/-- The reciprocal of the erased product with the reflected shift, supported on
its nonzero parity modes at resonance. -/
def highInverse (ε : ℤ) (r : ℕ) (z : ℂ) (j : ℤ) : ℂ :=
  if Even (j - ε) ∧ ε + 2 * (r : ℤ) + 1 < |j| then -(shiftedTail ε r (-z) j)⁻¹ else 0

private theorem cutoff_cast (hε : ε = 0 ∨ ε = 1) (hℓ : ℓ = ε.toNat + 2 * r + 1) :
    (ℓ : ℂ) = (ε : ℂ) + 2 * r + 1 := by
  have he : (ε.toNat : ℤ) = ε := Int.toNat_of_nonneg (by omega)
  have he' : (ε.toNat : ℂ) = ε := by exact_mod_cast he
  rw [hℓ]
  push_cast
  rw [he']

theorem residue_ne_zero (hε : ε = 0 ∨ ε = 1) (r : ℕ) : residue ε r ≠ 0 :=
  regularized_base_ne_zero hε r

theorem shiftedTail_symmetric (hε : ε = 0 ∨ ε = 1) (r : ℕ) (z : ℂ) :
    IsSymmetric ε ((-1 : ℂ) ^ ε.natAbs) (shiftedTail ε r z) :=
  isSymmetric_regularizedMultiplier _ hε r

theorem highInverse_symmetric (hε : ε = 0 ∨ ε = 1) (r : ℕ) (z : ℂ) :
    IsSymmetric ε ((-1 : ℂ) ^ ε.natAbs) (highInverse ε r z) := by
  intro j hj
  have hneg : Even (-j - ε) := by
    obtain ⟨s, hs⟩ := hj
    exact ⟨-s - ε, by omega⟩
  have hs := (shiftedTail_symmetric hε r (-z)).inv j hj
  simp only [← inv_pow, inv_neg, inv_one] at hs
  by_cases hcut : ε + 2 * (r : ℤ) + 1 < |j|
  · simpa only [highInverse, abs_neg, hj, hneg, hcut, and_self, ite_true, mul_neg] using
      congrArg Neg.neg hs
  · simp [highInverse, hcut]

theorem analyticAt_shiftedTail (ε j : ℤ) (r : ℕ) :
    AnalyticAt ℂ (fun z => shiftedTail ε r z j) 0 := by
  have ha : AnalyticAt ℂ (fun z : ℂ => -((ε : ℂ) + 2 * r + 1) + z) 0 :=
    analyticAt_const.add analyticAt_id
  exact (analyticAt_regularizedMultiplier_at_pole ε j r).comp_of_eq ha (add_zero _)

theorem analyticAt_highInverse (hε : ε = 0 ∨ ε = 1) (r : ℕ) (j : ℤ) :
    AnalyticAt ℂ (fun z => highInverse ε r z j) 0 := by
  unfold highInverse
  split_ifs with hj
  · have ha : AnalyticAt ℂ (fun z => shiftedTail ε r (-z) j) 0 :=
      (analyticAt_shiftedTail ε j r).comp_of_eq analyticAt_id.neg (neg_zero : -(0 : ℂ) = 0)
    have hnz : shiftedTail ε r (-(0 : ℂ)) j ≠ 0 := by
      simpa only [shiftedTail, neg_zero, add_zero] using
        (regularizedMultiplier_at_pole_ne_zero_iff hε r hj.1).mpr hj.2
    exact (ha.inv hnz).neg
  · exact analyticAt_const

theorem shiftedTail_of_ne (hε : ε = 0 ∨ ε = 1) (hℓ : ℓ = ε.toNat + 2 * r + 1)
    {z : ℂ} (hz : z ≠ 0) (j : ℤ) :
    shiftedTail ε r z j = z * genericMultiplier (-(ℓ : ℂ) + z) ε j := by
  have hp : (ε : ℂ) + 2 * r + 1 + (-((ε : ℂ) + 2 * r + 1) + z) = z := by ring
  have hp0 : (ε : ℂ) + 2 * r + 1 + (-((ε : ℂ) + 2 * r + 1) + z) ≠ 0 := by
    rw [hp]
    exact hz
  rw [shiftedTail, regularizedMultiplier_eq_mul_genericMultiplier ε r hp0, hp,
    cutoff_cast hε hℓ]

theorem shiftedTail_zero (hε : ε = 0 ∨ ε = 1) (hℓ : ℓ = ε.toNat + 2 * r + 1) (j : ℤ) :
    shiftedTail ε r 0 j = residue ε r * tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j := by
  simpa only [shiftedTail, add_zero, residue] using regularizedMultiplier_eq_tail hε r hℓ j

theorem highInverse_of_ne (hε : ε = 0 ∨ ε = 1) (hℓ : ℓ = ε.toNat + 2 * r + 1)
    {z : ℂ} (hz : z ≠ 0) {j : ℤ} (hj : Even (j - ε)) (hcut : (ℓ : ℤ) < |j|) :
    highInverse ε r z j = z⁻¹ * genericMultiplier ((ℓ : ℂ) + z) ε j := by
  have hc : ε + 2 * (r : ℤ) + 1 < |j| := by omega
  rw [highInverse, ite_eq_left ⟨hj, hc⟩, shiftedTail_of_ne hε hℓ (neg_ne_zero.mpr hz),
    show -(ℓ : ℂ) + -z = -((ℓ : ℂ) + z) by ring, genericMultiplier_neg]
  simp [mul_comm]

theorem highInverse_zero (hε : ε = 0 ∨ ε = 1) (hℓ : ℓ = ε.toNat + 2 * r + 1)
    {j : ℤ} (hj : Even (j - ε)) :
    highInverse ε r 0 j = -(residue ε r)⁻¹ * (tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j)⁻¹ := by
  by_cases hcut : (ℓ : ℤ) < |j|
  · have hc : ε + 2 * (r : ℤ) + 1 < |j| := by omega
    rw [highInverse, ite_eq_left ⟨hj, hc⟩, neg_zero, shiftedTail_zero hε hℓ]
    simp [mul_comm]
  · have hc : ¬ ε + 2 * (r : ℤ) + 1 < |j| := by omega
    have hpar : Even ((ℓ : ℤ) - 1 - ε) := ⟨r, by omega⟩
    have ht : tailMultiplier ℓ ε ((-1 : ℂ) ^ ε.natAbs) j = 0 := by
      by_contra hne
      exact hcut ((tailMultiplier_ne_zero_iff (by omega) hε hpar (neg_one_pow_sq _) hj).mp hne)
    simp [highInverse, hc, ht]

end Langlands.Archimedean.RealResonantHighInverse

namespace Langlands.Archimedean

open RealBlockMultiplier RealResonantHighInverse

/-- On a resonant parity class the shifted tail and its masked high inverse
are analytic at zero, with explicit generic and tail normalizations. -/
def RealResonantHighInverseStatement : Prop :=
  ∀ (ε : ℤ) (r : ℕ), (ε = 0 ∨ ε = 1) →
    let ℓ := ε.toNat + 2 * r + 1
    let σ := (-1 : ℂ) ^ ε.natAbs
    residue ε r ≠ 0 ∧
    (∀ z, IsSymmetric ε σ (shiftedTail ε r z) ∧ IsSymmetric ε σ (highInverse ε r z)) ∧
    (∀ j, AnalyticAt ℂ (fun z => shiftedTail ε r z j) 0 ∧
      AnalyticAt ℂ (fun z => highInverse ε r z j) 0) ∧
    (∀ z : ℂ, z ≠ 0 → ∀ j,
      shiftedTail ε r z j = z * genericMultiplier (-(ℓ : ℂ) + z) ε j ∧
      (Even (j - ε) → (ℓ : ℤ) < |j| →
        highInverse ε r z j = z⁻¹ * genericMultiplier ((ℓ : ℂ) + z) ε j)) ∧
    (∀ j, shiftedTail ε r 0 j = residue ε r * tailMultiplier ℓ ε σ j ∧
      (Even (j - ε) → highInverse ε r 0 j =
        -(residue ε r)⁻¹ * (tailMultiplier ℓ ε σ j)⁻¹))

theorem realResonantHighInverse : RealResonantHighInverseStatement := by
  intro ε r hε
  refine ⟨residue_ne_zero hε r, fun z => ⟨shiftedTail_symmetric hε r z,
    highInverse_symmetric hε r z⟩, fun j => ⟨analyticAt_shiftedTail ε j r,
    analyticAt_highInverse hε r j⟩, ?_, ?_⟩
  · exact fun z hz j => ⟨shiftedTail_of_ne hε rfl hz j, highInverse_of_ne hε rfl hz⟩
  · exact fun j => ⟨shiftedTail_zero hε rfl j, highInverse_zero hε rfl⟩

end Langlands.Archimedean
