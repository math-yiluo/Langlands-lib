import Langlands.Representation.Hecke.Convolution
import Langlands.Representation.RankinSelberg.Measures
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! # Normalized compact-open indicators and their averaging identities -/

noncomputable section

open MeasureTheory MeasureTheory.Measure Set Function

namespace Langlands.Hecke

open HarmonicAnalysis (SchwartzBruhat)

universe u

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G]

namespace HeckeAlgebra

variable (μ : Measure G) (K : OpenSubgroup G) (hK : IsCompact (K : Set G))

/-- The actual normalized subgroup indicator, for the measure defining convolution. -/
def normalizedIndicator : HeckeAlgebra μ :=
  ((μ.real (K : Set G) : ℂ)⁻¹) • TestFunction.subgroupIndicator K hK

omit [BorelSpace G] in
@[simp] theorem normalizedIndicator_apply (x : G) :
    normalizedIndicator μ K hK x =
      (μ.real (K : Set G) : ℂ)⁻¹ * (K : Set G).indicator (fun _ => (1 : ℂ)) x := rfl

omit [BorelSpace G] in
theorem normalizedIndicator_mem_biInvariant :
    (normalizedIndicator μ K hK : SchwartzBruhat G) ∈
      TestFunction.biInvariant K.toSubgroup K.toSubgroup :=
  (TestFunction.biInvariant K.toSubgroup K.toSubgroup).smul_mem _
    (TestFunction.subgroupIndicator_mem K hK)

variable [μ.IsHaarMeasure]

include hK in
omit [IsTopologicalGroup G] [BorelSpace G] in
/-- Positivity and finiteness are consequences of genuine Haar data. -/
theorem compactOpen_mass_pos : 0 < μ.real (K : Set G) :=
  ENNReal.toReal_pos (ne_of_gt (K.isOpen.measure_pos μ ⟨1, K.one_mem⟩)) hK.measure_ne_top

include hK in
omit [IsTopologicalGroup G] [BorelSpace G] in
theorem compactOpen_complex_mass_ne_zero : (μ.real (K : Set G) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ne_of_gt (compactOpen_mass_pos μ K hK))

omit [μ.IsHaarMeasure] in
/-- Left averaging has the inverse on the subgroup variable. -/
theorem normalizedIndicator_mul_apply (f : HeckeAlgebra μ) (x : G) :
    (normalizedIndicator μ K hK * f) x =
      (μ.real (K : Set G) : ℂ)⁻¹ * ∫ k in (K : Set G), f (k⁻¹ * x) ∂μ := by
  rw [mul_apply, ← integral_const_mul, ← integral_indicator K.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with k
  by_cases hk : k ∈ K <;> simp [normalizedIndicator_apply, hk]

/-- Right averaging uses `x*k`; left translation suffices, with no modular factor. -/
theorem mul_normalizedIndicator_apply (f : HeckeAlgebra μ) (x : G) :
    (f * normalizedIndicator μ K hK) x =
      (μ.real (K : Set G) : ℂ)⁻¹ * ∫ k in (K : Set G), f (x * k) ∂μ := by
  rw [mul_apply, ← integral_mul_left_eq_self
    (fun y => f y * normalizedIndicator μ K hK (y⁻¹ * x)) x]
  rw [← integral_const_mul, ← integral_indicator K.isOpen.measurableSet]
  apply integral_congr_ae
  filter_upwards [] with k
  simp only [mul_inv_rev, mul_assoc]
  by_cases hk : k ∈ K <;> simp [normalizedIndicator_apply, hk, mul_comm]

/-- The left average fixes every left-K-invariant actual test function. -/
theorem normalizedIndicator_mul_of_leftInvariant (f : HeckeAlgebra μ)
    (hf : ∀ k : K, ∀ x, f ((k : G) * x) = f x) :
    normalizedIndicator μ K hK * f = f := by
  ext x
  rw [normalizedIndicator_mul_apply]
  have h : (∫ k in (K : Set G), f (k⁻¹ * x) ∂μ) =
      (μ.real (K : Set G) : ℂ) * f x := by
    rw [← Complex.real_smul, ← setIntegral_const]
    apply setIntegral_congr_fun K.isOpen.measurableSet
    intro k hk
    exact hf ⟨k⁻¹, K.inv_mem hk⟩ x
  rw [h, ← mul_assoc, inv_mul_cancel₀ (compactOpen_complex_mass_ne_zero μ K hK), one_mul]

/-- The right average fixes every right-K-invariant actual test function. -/
theorem mul_normalizedIndicator_of_rightInvariant (f : HeckeAlgebra μ)
    (hf : ∀ k : K, ∀ x, f (x * (k : G)) = f x) :
    f * normalizedIndicator μ K hK = f := by
  ext x
  rw [mul_normalizedIndicator_apply]
  have h : (∫ k in (K : Set G), f (x * k) ∂μ) =
      (μ.real (K : Set G) : ℂ) * f x := by
    rw [← Complex.real_smul, ← setIntegral_const]
    apply setIntegral_congr_fun K.isOpen.measurableSet
    intro k hk
    exact hf ⟨k, hk⟩ x
  rw [h, ← mul_assoc, inv_mul_cancel₀ (compactOpen_complex_mass_ne_zero μ K hK), one_mul]

/-- The normalized subgroup indicator is a convolution idempotent. -/
theorem normalizedIndicator_idempotent :
    normalizedIndicator μ K hK * normalizedIndicator μ K hK = normalizedIndicator μ K hK :=
  normalizedIndicator_mul_of_leftInvariant μ K hK _
    (normalizedIndicator_mem_biInvariant μ K hK).1

/-- Refining the subgroup gives a left local unit for the larger indicator. -/
theorem normalizedIndicator_mul_of_le (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hLK : L ≤ K) :
    normalizedIndicator μ L hL * normalizedIndicator μ K hK = normalizedIndicator μ K hK :=
  normalizedIndicator_mul_of_leftInvariant μ L hL _
    (fun l x => (normalizedIndicator_mem_biInvariant μ K hK).1 ⟨l, hLK l.property⟩ x)

/-- Refining the subgroup gives a right local unit for the larger indicator. -/
theorem normalizedIndicator_mul_of_ge (L : OpenSubgroup G) (hL : IsCompact (L : Set G))
    (hLK : L ≤ K) :
    normalizedIndicator μ K hK * normalizedIndicator μ L hL = normalizedIndicator μ K hK :=
  mul_normalizedIndicator_of_rightInvariant μ L hL _
    (fun l x => (normalizedIndicator_mem_biInvariant μ K hK).2 ⟨l, hLK l.property⟩ x)

end HeckeAlgebra

/-- With the existing Haar measure normalized on K, the idempotent is exactly `1_K`. -/
theorem normalizedIndicator_normalizedHaar (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (HeckeAlgebra.normalizedIndicator (RankinSelberg.normalizedCompactOpenHaar K hK) K hK :
      SchwartzBruhat G) = TestFunction.subgroupIndicator K hK := by
  apply TestFunction.ext
  intro x
  change HeckeAlgebra.normalizedIndicator _ K hK x = _
  simp [HeckeAlgebra.normalizedIndicator_apply, Measure.real,
    RankinSelberg.normalizedCompactOpenHaar_self]

end Langlands.Hecke
