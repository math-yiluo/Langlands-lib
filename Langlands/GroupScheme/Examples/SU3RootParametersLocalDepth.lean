import Langlands.GroupScheme.Examples.SU3RootValuation
import Langlands.GroupScheme.Examples.SU3RootParametersLocalValuation
import Mathlib.Data.Int.Interval
import Mathlib.Algebra.Order.Floor.Ring

/-! # Discrete depths on actual quadratic local-field root coordinates -/

noncomputable section

open Algebra

universe u v

namespace Langlands.GroupScheme.SU3Root

variable (F : Type u) (L : Type v) [Field F] [Field L] [Algebra F L]
  [IsQuadraticExtension F L] [Algebra.IsSeparable F L]
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- The unshifted multipliable-root depth for the actual quadratic extension. -/
def quadraticDepth (p : rationalParameters F L) : WithTop ℝ :=
  Parameters.depthA (quadraticValuation F L) p

/-- The unshifted depth on the literal central coordinate subgroup. -/
def quadraticCentralDepth (z : Parameters.central (fieldInvolution F L)) : WithTop ℝ :=
  Parameters.depthDouble (quadraticValuation F L) z

/-- Finite root depths are contained in the quarter-integers. -/
theorem quadraticDepth_exists_quarter_integer {p : rationalParameters F L} (hp : p ≠ 1) :
    ∃ n : ℤ, quadraticDepth F L p = ((n : ℝ) / 4 : ℝ) := by
  have hv : p.second ≠ 0 := by
    intro h
    exact hp ((Parameters.second_eq_zero_iff p).mp h)
  obtain ⟨n, hn⟩ := quadraticValuation_exists_half_integer F L hv
  refine ⟨n, ?_⟩
  change halfTop (quadraticValuation F L p.second) = _
  rw [hn, halfTop_coe]
  congr 1
  ring

/-- Finite central depths are contained in the half-integers. -/
theorem quadraticCentralDepth_exists_half_integer
    {z : Parameters.central (fieldInvolution F L)} (hz : z ≠ 1) :
    ∃ n : ℤ, quadraticCentralDepth F L z = ((n : ℝ) / 2 : ℝ) := by
  have hv : z.val.second ≠ 0 := by
    intro h
    exact hz (Subtype.ext ((Parameters.second_eq_zero_iff z.val).mp h))
  exact quadraticValuation_exists_half_integer F L hv

/-- Nonidentity central parameters have arbitrarily large finite depths for both roots. -/
theorem exists_central_parameter_of_depth_ge (r : ℝ) :
    ∃ z : Parameters.central (fieldInvolution F L),
      z ≠ 1 ∧
      (r : WithTop ℝ) ≤ quadraticDepth F L z.val ∧
      (r : WithTop ℝ) ≤ quadraticCentralDepth F L z := by
  obtain ⟨p, hp, hv, hbound⟩ :=
    exists_central_parameter_of_value_ge F L (max (2 * r) r)
  refine ⟨⟨p, hp⟩, ?_, ?_, ?_⟩
  · intro h
    have hval : p = 1 := congrArg Subtype.val h
    exact hv ((Parameters.second_eq_zero_iff p).mpr hval)
  · apply (coe_le_halfTop_iff r (quadraticValuation F L p.second)).mpr
    exact (WithTop.coe_le_coe.mpr (le_max_left (2 * r) r)).trans hbound
  · exact (WithTop.coe_le_coe.mpr (le_max_right (2 * r) r)).trans hbound

private theorem finite_integer_div_values (d a b : ℝ) (hd : 0 < d) :
    Set.Finite {t : ℝ | a ≤ t ∧ t ≤ b ∧ ∃ n : ℤ, t = (n : ℝ) / d} := by
  apply ((Set.finite_Icc (⌈a * d⌉ : ℤ) ⌊b * d⌋).image
    (fun n : ℤ => (n : ℝ) / d)).subset
  rintro t ⟨hat, htb, n, rfl⟩
  exact ⟨n, ⟨Int.ceil_le.mpr ((le_div_iff₀ hd).mp hat),
    Int.le_floor.mpr ((div_le_iff₀ hd).mp htb)⟩, rfl⟩

/-- Only finitely many real root-depth values occur in a bounded interval. -/
theorem quadraticDepth_finite_Icc (a b : ℝ) :
    Set.Finite {t : ℝ | a ≤ t ∧ t ≤ b ∧
      ∃ p : rationalParameters F L, quadraticDepth F L p = t} := by
  apply (finite_integer_div_values 4 a b (by norm_num)).subset
  rintro t ⟨hat, htb, p, hpt⟩
  have hp : p ≠ 1 := by
    intro hp
    simp [hp, quadraticDepth, Parameters.depthA] at hpt
  obtain ⟨n, hn⟩ := quadraticDepth_exists_quarter_integer F L hp
  refine ⟨hat, htb, n, ?_⟩
  exact WithTop.coe_inj.mp (hpt.symm.trans hn)

/-- Only finitely many real central-depth values occur in a bounded interval. -/
theorem quadraticCentralDepth_finite_Icc (a b : ℝ) :
    Set.Finite {t : ℝ | a ≤ t ∧ t ≤ b ∧
      ∃ z : Parameters.central (fieldInvolution F L),
        quadraticCentralDepth F L z = t} := by
  apply (finite_integer_div_values 2 a b (by norm_num)).subset
  rintro t ⟨hat, htb, z, hzt⟩
  have hz : z ≠ 1 := by
    intro hz
    simp [hz, quadraticCentralDepth, Parameters.depthDouble] at hzt
  obtain ⟨n, hn⟩ := quadraticCentralDepth_exists_half_integer F L hz
  refine ⟨hat, htb, n, ?_⟩
  exact WithTop.coe_inj.mp (hzt.symm.trans hn)

end Langlands.GroupScheme.SU3Root
