import Langlands.Global.RankinSelberg.ComplexJacquetContinuationStep
import Langlands.Global.RankinSelberg.ComplexRankZeroWhittaker
import Langlands.Representation.RankinSelberg.RankOneGammaTwistAlgebra

/-! # The rank-one base of uniform Jacquet continuation -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open ArchimedeanLocal (archimedeanComplexNMeasurable archimedeanComplexNBorel)
open ComplexCompactProfileFamily (characterList IsCompactProfile standardSection standardSection_mem
  differentiable_standardSection)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetUnipotentMeasure (entryHaar)
open ComplexLocalIwasawa (alpha npart kpart npart_mul_logTorus_mul_kpart)
open ComplexLocalOrdinaryConvergence (norm_detPower_logTorus_mul)
open ComplexRankZero (characterFunction eq_mul_characterFunction)
open Langlands.Archimedean (characterOfParams characterOfParams_exponent)
open Langlands.GeneralLinear (UpperEntryPair upperEntryCoordinates upperEntryProductMeasure)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open Langlands.RankinSelberg.RankOneGammaTwist (weylLong_one)
open RealConvergenceAnalysis (rootPos norm_cexp_mul_ofReal)

attribute [local instance] archimedeanComplexNMeasurable archimedeanComplexNBorel

local notation "G" => Langlands.GeneralLinear (0 + 1) ℂ
local notation "P" => Fin (0 + 1) → ℂ
local notation "U" => Matrix.unitaryGroup (Fin (0 + 1)) ℂ
local notation "N₁" => Langlands.GeneralLinear.upperUnipotent (0 + 1) ℂ
local instance : Unique (Fin (0 + 1)) := inferInstanceAs (Unique (Fin 1))
local instance : Subsingleton N₁ :=
  Langlands.RankinSelberg.upperUnipotent_one_subsingleton

private theorem entryHaar_one_univ (μ : AdditiveHaarMeasure ℂ) : entryHaar μ 1 univ = 1 := by
  let : IsEmpty (UpperEntryPair 1) := ⟨fun ij => (ne_of_lt ij.2) (Subsingleton.elim _ _)⟩
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  rw [entryHaar, Measure.map_apply (upperEntryCoordinates (K := ℂ) 1).symm.measurable MeasurableSet.univ,
    preimage_univ, upperEntryProductMeasure, Measure.pi_univ, Finset.prod_of_isEmpty]

/-- The rank-one open-cell integral is the section itself with entry-product Haar. -/
theorem openCellIntegral_rankOne (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (f : G → ℂ) (g : G) :
    openCellIntegral (j := 0) a (entryHaar μ 1) f g = f g := by
  have hconst (u : N₁) :
      f (GeneralLinear.weylLong 1 ℂ * u.val * g) * complexWhittakerCharacter (r := 0) a u.val = f g := by
    rw [Subsingleton.elim u 1, weylLong_one, OneMemClass.coe_one, one_mul, one_mul]
    simp [complexWhittakerCharacter]
  unfold openCellIntegral
  simp_rw [hconst]
  rw [integral_const, Measure.real, entryHaar_one_univ, ENNReal.toReal_one, one_smul]

private theorem norm_characterFunction (d : ComplexCharacterData) (g : G) :
    ‖characterFunction d g‖ = Real.exp (2 * d.exponent.re * alpha g 0) := by
  have hg : ComplexLocalWhittakerGauge.logTorus (alpha g) * (kpart g).val = g := by
    simpa only [Subsingleton.elim (npart g) 1, OneMemClass.coe_one, one_mul]
      using npart_mul_logTorus_mul_kpart g
  have hh := norm_detPower_logTorus_mul (alpha g) (kpart g) d.exponent
  rw [hg, Fin.sum_univ_one] at hh
  change ‖Complex.exp (d.exponent * (Real.log (‖g.val.det‖ ^ 2) : ℂ))‖ = _ at hh
  rw [norm_cexp_mul_ofReal, Real.log_pow] at hh
  rw [characterFunction, Langlands.Archimedean.ComplexSwapJacquet.norm_character]
  change ‖g.val.det‖ ^ (2 * d.exponent.re) = _
  rw [Real.rpow_def_of_pos (norm_pos_iff.mpr g.det_ne_zero), ← hh]
  congr 1
  push_cast
  ring

private theorem norm_standardSection_rankOne {l : Fin (0 + 1) → ℤ} {φ : U → ℂ}
    (hφ : IsCompactProfile l φ) (p : P) (g : G) :
    ‖standardSection p φ g‖ = ‖φ 1‖ * Real.exp (2 * (p 0).re * alpha g 0) := by
  let d := characterOfParams (l 0) (p 0)
  have hlist : characterList l p = [d] := by simp only [characterList, List.ofFn_succ, List.ofFn_zero, d]
  have hmem : standardSection p φ ∈ Langlands.Archimedean.complexStandardModule (0 + 1) (characterList l p) :=
    (standardSection_mem hφ p).1
  rw [hlist] at hmem
  have heval : standardSection p φ (1 : G) = φ 1 := by
    simpa only [map_one] using ComplexCompactProfileFamily.standardSection_unitary p φ 1
  rw [eq_mul_characterFunction d hmem, heval, norm_mul, norm_characterFunction, characterOfParams_exponent]

private theorem uniform_simpleRootBound_rankOne {l : Fin (0 + 1) → ℤ} {φ : U → ℂ}
    (hφ : IsCompactProfile l φ) (p₀ : P) :
    ComplexGodementWhittakerFamily.HasUniformSimpleRootBound (r := 0) (Metric.ball p₀ 1)
      (fun p => standardSection p φ) := by
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * (‖p₀‖ + 1))
  refine ⟨N, fun J => ⟨‖φ 1‖, norm_nonneg _, ?_⟩⟩
  intro p hp g
  change ‖standardSection p φ g‖ ≤ ‖φ 1‖ *
    Real.exp ((N : ℝ) * (∑ i : Fin 1, |alpha g i|) - (J : ℝ) * rootPos (r := 0) (alpha g))
  simp only [norm_standardSection_rankOne hφ, rootPos, Finset.univ_eq_empty, Finset.sum_empty,
    mul_zero, sub_zero, Fin.sum_univ_one]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  apply Real.exp_le_exp.mpr
  have hp₀ : ‖p‖ ≤ ‖p₀‖ + 1 := by
    have hp' : ‖p - p₀‖ < 1 := by simpa only [Metric.mem_ball, dist_eq_norm] using hp
    calc
      ‖p‖ = ‖(p - p₀) + p₀‖ := by rw [sub_add_cancel]
      _ ≤ ‖p - p₀‖ + ‖p₀‖ := norm_add_le _ _
      _ ≤ ‖p₀‖ + 1 := by linarith
  have hb : 2 * |(p 0).re| ≤ (N : ℝ) := by
    have hre := (Complex.abs_re_le_norm (p 0)).trans (norm_le_pi_norm p 0)
    linarith
  calc
    2 * (p 0).re * alpha g 0 ≤ |2 * (p 0).re * alpha g 0| := le_abs_self _
    _ = 2 * |(p 0).re| * |alpha g 0| := by rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
    _ ≤ (N : ℝ) * |alpha g 0| := mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-- The rank-one continuation has continuous group slices, entire parameter values and the
locally uniform estimates required by the Godement continuation step. -/
def ComplexJacquetRankOneStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ), HasLocallyUniformJacquetFamily 0 μ a

theorem complexJacquetRankOne : ComplexJacquetRankOneStatement := by
  intro μ a
  unfold HasLocallyUniformJacquetFamily
  intro l φ hφ
  refine ⟨fun p => standardSection p φ, ?_, differentiable_standardSection φ,
    fun p => ⟨1, zero_lt_one, uniform_simpleRootBound_rankOne hφ p⟩, ?_⟩
  · intro p
    change Continuous (standardSection (n := 0 + 1) p φ)
    exact (standardSection_mem hφ p).1.1.continuous
  · intro p _ g
    exact (openCellIntegral_rankOne μ a (standardSection p φ) g).symm

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation
