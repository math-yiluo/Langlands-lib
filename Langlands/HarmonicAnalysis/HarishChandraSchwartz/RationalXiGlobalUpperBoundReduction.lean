import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanIwasawaWeightComparisonStatement
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiGlobalUpperBoundStatement

/-! # Globalizing the actual chamber Xi upper bound -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- The actual chamber upper bound and actual Cartan/Iwasawa weight comparison
imply the global upper bound, with a natural exponent and a positive constant. -/
theorem rationalXiGlobalUpperBound_of_chamber_of_comparison
    (hupper : RationalXiUpperBoundStatement.{u})
    (hcomparison : RationalCartanIwasawaWeightComparisonStatement.{u}) :
    RationalXiGlobalUpperBoundStatement.{u} := by
  intro F _ _ _ _ G _ _ hG S i hi ν hν K0 hK0o hK0c hbasis hcover K hKo hKc hPK N _ ρ hρ
  obtain ⟨F0, hF0⟩ := hcover
  have hbasis' := hbasis
  obtain ⟨Bs, -, hBJ⟩ := hbasis'
  obtain ⟨-, A, q, hA, -⟩ := hBJ ∅ (Set.empty_subset _)
  have hexists : ∃ ζ, IsStandardCocharacter i ν ∅ ζ :=
    ⟨ν, isStandardCocharacter_empty_self i ν⟩
  let Idx := {y : cocharacterLattice S //
    ∀ β : Aubert.General.RationalPointFamily.SimpleRoot i ν,
      0 ≤ Aubert.General.simpleRootPairing i ν β y}
  have hCA (y : Idx) : Aubert.General.uniformizerPowers i (.ofAdd y.1) ∈
      standardComponentCAplus i ν ∅ q :=
    (uniformizerPowers_mem_standardComponentChambers hi hexists hA y.1 (by simp)
      fun β hβ => by simpa using y.2 ⟨β, hβ⟩).2
  have hP (y : Idx) : Aubert.General.uniformizerPowers i (.ofAdd y.1) ∈
      standardParabolicPoints i ν ∅ :=
    mem_standardParabolicPoints_of_mem_standardComponentCAplus hA (hCA y)
  obtain ⟨B, hB⟩ := exists_rationalHeight_uniformizerPowers_le ρ hK0c F0
  set B' := max B 0
  have hB'0 : 0 ≤ B' := le_max_right _ _
  have hσ (y : Idx) (g : rationalPoints G) (hg : g ∈ rationalCartanCell i K0 F0 y.1) :
      1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y.1)) ≤
        (1 + B') * (1 + rationalHeight (F := F) ρ g) := by
    have h1 := hB y.1 g hg
    have h2 := rationalHeight_nonneg (F := F) ρ g
    have h3 : B ≤ B' := le_max_left _ _
    nlinarith
  obtain ⟨d, hd⟩ := hupper F G hG S i hi ν hν K0 hbasis A q hA K hKo hKc hPK N ρ hρ
  obtain ⟨M, hM⟩ := exists_rationalXi_le_of_mem_rationalCartanCell hK0c F0 hKo hKc hPK
    (P := fun a => a ∈ standardParabolicPoints i ν ∅ ∧ a ∈ standardComponentCAplus i ν ∅ q)
    (Φ := fun a ha => (NNReal.sqrt (rationalMinimalModulus i ν ⟨a, ha.1⟩ : ℝ≥0) : ℝ) *
      (1 + rationalHeight (F := F) ρ a) ^ d)
    (fun a _ => mul_nonneg (NNReal.coe_nonneg _)
      (pow_nonneg (by linarith [rationalHeight_nonneg (F := F) ρ a]) _))
    (fun g₁ g₂ => by
      obtain ⟨C, hC⟩ := hd g₁ g₂
      exact ⟨C, fun a ha => by rw [← mul_assoc]; exact hC a ha.1 ha.2⟩)
  obtain ⟨Cw, hCw, hw⟩ := hcomparison F G hG S i hi ν hν K0 hK0c F0 K hKo hKc hPK
  have hMpos : 0 < max M 1 := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  refine ⟨d, max M 1 * Cw * (1 + B') ^ d,
    mul_pos (mul_pos hMpos hCw) (pow_pos (by linarith) _), fun g => ?_⟩
  obtain ⟨y, hy, hg⟩ := exists_mem_rationalCartanCell hF0 g
  let z : Idx := ⟨y, hy⟩
  have hweight := iwasawaWeight_mul (hPK := hPK)
    (fun p hp => rationalMinimalModulus_eq_one i ν hKo hKc p hp) (hP z) K.one_mem
  rw [mul_one] at hweight
  have hweightle : (NNReal.sqrt (rationalMinimalModulus i ν ⟨_, hP z⟩ : ℝ≥0) : ℝ) ≤
      Cw * iwasawaWeight hPK (rationalMinimalModulus i ν) g := by
    rw [← hweight]
    exact hw y hy g hg
  have hheighty := rationalHeight_nonneg (F := F) ρ
    (Aubert.General.uniformizerPowers i (.ofAdd y))
  have hheightg := rationalHeight_nonneg (F := F) ρ g
  have hpower : (1 + rationalHeight (F := F) ρ
      (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ d ≤
      (1 + B') ^ d * (1 + rationalHeight (F := F) ρ g) ^ d := by
    rw [← mul_pow]
    gcongr
    exact hσ z g hg
  calc rationalXi hKc hPK g ≤
      M * ((NNReal.sqrt (rationalMinimalModulus i ν ⟨_, hP z⟩ : ℝ≥0) : ℝ) *
        (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ d) :=
      hM y ⟨hP z, hCA z⟩ g hg
    _ ≤ max M 1 * ((NNReal.sqrt (rationalMinimalModulus i ν ⟨_, hP z⟩ : ℝ≥0) : ℝ) *
        (1 + rationalHeight (F := F) ρ (Aubert.General.uniformizerPowers i (.ofAdd y))) ^ d) := by
      apply mul_le_mul_of_nonneg_right (le_max_left _ _)
      exact mul_nonneg (NNReal.coe_nonneg _) (pow_nonneg (by linarith) d)
    _ ≤ max M 1 * ((Cw * iwasawaWeight hPK (rationalMinimalModulus i ν) g) *
        ((1 + B') ^ d * (1 + rationalHeight (F := F) ρ g) ^ d)) := by
      apply mul_le_mul_of_nonneg_left _ hMpos.le
      exact mul_le_mul hweightle hpower (pow_nonneg (by linarith) d)
        (mul_nonneg hCw.le (iwasawaWeight_nonneg _))
    _ = _ := by ring

end Langlands.HarishChandraSchwartz
