import Langlands.Representation.RankinSelberg.AdjacentRankCompactOrbit
import Langlands.Representation.Hecke.ActionIntegrand
import Langlands.HarmonicAnalysis.AlgebraicIntegral
import Mathlib.MeasureTheory.Group.Measure

/-! Finite algebraic integration on the compact rectangular orbit. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Matrix

universe uF uV

variable {K : Type uF} [Field K] [TopologicalSpace K]
  [IsTopologicalDivisionRing K] [T2Space K] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Rectangular tests whose entire topological support has full row rank. -/
def adjacentRankCompactTests (n : ℕ) (K : Type uF) [Field K] [TopologicalSpace K] :
    Submodule ℂ (SchwartzBruhat (Matrix (Fin n) (Fin (n + 1)) K)) where
  carrier := {Φ | ∀ M ∈ tsupport (Φ : _ → ℂ), AdjacentRankFullRank M}
  zero_mem' := by simp
  add_mem' := by
    intro Φ Ψ hΦ hΨ M hM
    rcases tsupport_add (Φ : _ → ℂ) (Ψ : _ → ℂ) hM with hM | hM
    · exact hΦ M hM
    · exact hΨ M hM
  smul_mem' := by
    intro c Φ hΦ M hM
    exact hΦ M (tsupport_smul_subset_right (fun _ => c) (Φ : _ → ℂ) hM)

variable [MeasurableSpace (GeneralLinear n K)] [OpensMeasurableSpace (GeneralLinear n K)]

/-- The inner vector integrand of formula (10), using a smooth scalar weight.
The inverse orbit acts on an algebraic module with no topology. -/
def adjacentRankCompactIntegrand
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) :
    SimpleFunc (GeneralLinear n K) V := by
  let f : GeneralLinear n K → V :=
    fun h => (Φ.val (rectangularJoin h.val 0 * g.val) * (ξ h : ℂ)) • ρ h⁻¹ v
  have hmat : Continuous (fun h : GeneralLinear n K =>
      rectangularJoin h.val 0 * g.val) :=
    (continuous_rectangularJoin.comp
      (Units.continuous_val.prodMk continuous_const)).matrix_mul continuous_const
  have hlc : IsLocallyConstant f :=
    ((Φ.val.locallyConstant.comp_continuous hmat).mul hξ).comp₂
      ((Hecke.orbitMap_locallyConstant ρ (hρ v)).comp_continuous continuous_inv) (· • ·)
  have hc : HasCompactSupport f :=
    ((adjacentRankCompactOrbit_hasCompactSupport Φ.val Φ.property g).mul_right).smul_right
  exact compactlySupportedSimpleFunc f hlc hc

@[simp] theorem adjacentRankCompactIntegrand_apply
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V)
    (g : GeneralLinear (n + 1) K) (h : GeneralLinear n K) :
    adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g h =
      (Φ.val (rectangularJoin h.val 0 * g.val) * (ξ h : ℂ)) • ρ h⁻¹ v := rfl

theorem adjacentRankCompactIntegrand_finMeasSupp
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) :
    (adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g).FinMeasSupp μ := by
  apply SimpleFunc.finMeasSupp_iff_support.mpr
  have hc : HasCompactSupport (fun h : GeneralLinear n K =>
      (Φ.val (rectangularJoin h.val 0 * g.val) * (ξ h : ℂ)) • ρ h⁻¹ v) :=
    ((adjacentRankCompactOrbit_hasCompactSupport Φ.val Φ.property g).mul_right).smul_right
  exact lt_of_le_of_lt (measure_mono (subset_tsupport _)) hc.measure_lt_top

/-- The actual algebraic vector integral in formula (10), before its outer
determinant character. It is a finite sum in the original algebraic module. -/
def adjacentRankCompactAverage
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K) : V :=
  AlgebraicIntegral.integral μ (adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g)

/-- Every algebraic functional evaluates the finite vector integral as the
ordinary complex integral. Continuity of the functional is unnecessary. -/
theorem adjacentRankCompactAverage_dual
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v : V) (g : GeneralLinear (n + 1) K)
    (L : V →ₗ[ℂ] ℂ) :
    L (adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g) =
      ∫ h, Φ.val (rectangularJoin h.val 0 * g.val) * (ξ h : ℂ) * L (ρ h⁻¹ v) ∂μ := by
  unfold adjacentRankCompactAverage
  rw [← AlgebraicIntegral.integral_linearMap _
    (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g) L]
  rw [AlgebraicIntegral.integral_eq_bochner _
    ((adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g).map L.map_zero)]
  congr 1
  funext h
  simp

theorem adjacentRankCompactAverage_add
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (v w : V) (g : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ Φ (v + w) g =
      adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g +
        adjacentRankCompactAverage μ ρ hρ ξ hξ Φ w g := by
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ Φ (v + w) g =
      adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g +
        adjacentRankCompactIntegrand ρ hρ ξ hξ Φ w g := by
    ext h
    simp [smul_add]
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_add _
    _ (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g)
    (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ w g)]

theorem adjacentRankCompactAverage_smul
    (μ : Measure (GeneralLinear n K)) [IsFiniteMeasureOnCompacts μ]
    (ρ : Representation ℂ (GeneralLinear n K) V) (hρ : IsSmooth ρ)
    (ξ : GeneralLinear n K →* ℂˣ)
    (hξ : IsLocallyConstant (fun h => (ξ h : ℂ)))
    (Φ : adjacentRankCompactTests n K) (c : ℂ) (v : V) (g : GeneralLinear (n + 1) K) :
    adjacentRankCompactAverage μ ρ hρ ξ hξ Φ (c • v) g =
      c • adjacentRankCompactAverage μ ρ hρ ξ hξ Φ v g := by
  have he : adjacentRankCompactIntegrand ρ hρ ξ hξ Φ (c • v) g =
      c • adjacentRankCompactIntegrand ρ hρ ξ hξ Φ v g := by
    ext h
    simp [smul_smul, mul_comm]
  unfold adjacentRankCompactAverage
  rw [he, AlgebraicIntegral.integral_smul c _
    (adjacentRankCompactIntegrand_finMeasSupp μ ρ hρ ξ hξ Φ v g)]

end Langlands.RankinSelberg
