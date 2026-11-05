import Mathlib.MeasureTheory.Group.ModularCharacter
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.Algebra.Group.Pointwise

/-! # Continuity of the intrinsic modular character -/

noncomputable section

universe u

open MeasureTheory MeasureTheory.Measure Set
open scoped Topology Pointwise CompactlySupported NNReal

namespace Langlands.Haar

variable {G : Type u} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [LocallyCompactSpace G]

section Integral

variable [MeasurableSpace G] [BorelSpace G]
  (μ : Measure G) [IsFiniteMeasureOnCompacts μ]

/-- A right-translated compact continuous test has a continuous integral
against every measure finite on compact sets. -/
theorem continuous_integral_mul_right (f : C_c(G, ℝ)) :
    Continuous (fun g : G => ∫ x, f (x * g) ∂μ) := by
  rw [continuous_iff_continuousAt]
  intro g
  obtain ⟨U, hUc, hUg⟩ := exists_compact_mem_nhds g
  let K : Set G := tsupport f * U⁻¹
  have hK : IsCompact K := f.hasCompactSupport.mul hUc.inv
  have hc : ContinuousOn (fun p : G × G => f (p.2 * p.1)) (U ×ˢ univ) :=
    (f.continuous.comp (continuous_snd.mul continuous_fst)).continuousOn
  have hz : ∀ p, ∀ x : G, p ∈ U → x ∉ K → f (x * p) = 0 := by
    intro p x hp hx
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    apply hx
    exact ⟨x * p, hs, p⁻¹, by simpa, by simp⟩
  exact (continuousOn_integral_of_compact_support (μ := μ) hK hc hz).continuousAt hUg

/-- The actual modular value is the ratio of a translated Haar integral to a
fixed nonzero compact-test integral. -/
theorem coe_modularCharacter_eq_integral_div (f : C_c(G, ℝ))
    (hf : (∫ x, f x ∂(haar : Measure G)) ≠ 0) (g : G) :
    (modularCharacter g : ℝ) =
      (∫ x, f (x * g) ∂(haar : Measure G)) / ∫ x, f x ∂(haar : Measure G) := by
  calc
    (modularCharacter g : ℝ) =
        (haarScalarFactor (Measure.map (· * g) (haar : Measure G)) haar : ℝ) := by
      change (modularCharacterFun g : ℝ) = _
      rw [modularCharacterFun_eq_haarScalarFactor haar g]
    _ = (∫ x, f x ∂(Measure.map (· * g) (haar : Measure G))) / ∫ x, f x ∂haar :=
      haarScalarFactor_eq_integral_div _ _ f.continuous f.hasCompactSupport hf
    _ = _ := by rw [(measurableEmbedding_mulRight g).integral_map]

end Integral

/-- The intrinsic modular character of a locally compact topological group is
continuous, without a separation or countability hypothesis. -/
theorem continuous_modularCharacter_of_locallyCompact :
    Continuous (modularCharacter (G := G)) := by
  let : MeasurableSpace G := borel G
  let : BorelSpace G := ⟨rfl⟩
  obtain ⟨f, hfc, hf0, hf1⟩ :
      ∃ f : C(G, ℝ), HasCompactSupport f ∧ 0 ≤ f ∧ f 1 ≠ 0 :=
    exists_continuous_nonneg_pos 1
  let f₀ : C_c(G, ℝ) := ⟨f, hfc⟩
  have hfint : (∫ x, f₀ x ∂(haar : Measure G)) ≠ 0 :=
    ne_of_gt (f.continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero hfc hf0 hf1)
  apply NNReal.isEmbedding_coe.continuous_iff.mpr
  have hcont := (continuous_integral_mul_right (haar : Measure G) f₀).div_const
    (∫ x, f₀ x ∂(haar : Measure G))
  exact hcont.congr fun g => (coe_modularCharacter_eq_integral_div f₀ hfint g).symm

/-- Mathlib's intrinsic modular character as a continuous monoid homomorphism. -/
def continuousModularCharacter : G →ₜ* ℝ≥0 where
  toMonoidHom := modularCharacter
  continuous_toFun := continuous_modularCharacter_of_locallyCompact

@[simp] theorem continuousModularCharacter_apply (g : G) :
    continuousModularCharacter g = modularCharacter g := rfl

end Langlands.Haar
