import Langlands.Automorphic.OperatorDeterminantSliceHaar
import Langlands.Global.PrimitiveAdelicBounded
import Langlands.Global.SimpleRootBoxCompact
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! # Compact determinant-band representatives in rank one -/

noncomputable section
universe uF
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
open scoped NNReal CategoryTheory.MonObj

namespace Langlands.Global.IdeleAbsoluteValue

open scoped NNReal
variable (F : Type uF) [Field F] [NumberField F]

/-- A continuous positive scalar section of the normalized idelic absolute value. -/
def normSection : ℝ≥0ˣ →ₜ* Ideles F where
  toMonoidHom := (PositiveRealIdeles.full F).toMonoidHom.comp
    (Units.map (NNReal.rpowMonoidHom ((Module.finrank ℚ F : ℝ)⁻¹)))
  continuous_toFun := (PositiveRealIdeles.full F).continuous.comp
    ((NNReal.continuous_rpow_const (inv_nonneg.mpr (Nat.cast_nonneg _))).units_map _)

@[simp] theorem full_normSection (h : ℝ≥0ˣ) : full F (normSection F h) = h :=
  PrimitiveAdelicHeight.absoluteValue_scalarRoot F h

/-- A bounded positive-norm interval has a compact set of principal idele representatives. -/
theorem exists_isCompact_bandCover (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ K : Set (Ideles F), IsCompact K ∧
      ∀ z : Ideles F, lo ≤ ((full F z : ℝ≥0) : ℝ) ∧
        ((full F z : ℝ≥0) : ℝ) ≤ hi →
          ∃ a : Fˣ, diagonalUnits F a * z ∈ K := by
  obtain ⟨C, hC, _, hcover⟩ := NormOneIdeleClass.exists_isCompact_fundamentalSet F
  let B : Set ℝ≥0ˣ := {h | lo ≤ ((h : ℝ≥0) : ℝ) ∧ ((h : ℝ≥0) : ℝ) ≤ hi}
  let K : Set (Ideles F) := (fun p : ℝ≥0ˣ × Ideles F => normSection F p.1 * p.2) '' (B ×ˢ C)
  refine ⟨K, ((PositiveRealTorus.isCompact_unitsBox lo hi hlo).prod hC).image
    (((normSection F).continuous.comp continuous_fst).mul continuous_snd), ?_⟩
  intro z hz
  let s := normSection F (full F z)
  have hnorm : s⁻¹ * z ∈ NormOneIdeleClass.normOneIdeles F := by
    change full F (s⁻¹ * z) = 1
    simp only [map_mul, map_inv, s, full_normSection, inv_mul_cancel]
  obtain ⟨a, ha⟩ := hcover (s⁻¹ * z) hnorm
  refine ⟨a, ⟨(full F z, diagonalUnits F a * (s⁻¹ * z)), ⟨hz, ha⟩, ?_⟩⟩
  change s * (diagonalUnits F a * (s⁻¹ * z)) = diagonalUnits F a * z
  rw [mul_left_comm s, mul_inv_cancel_left]

end Langlands.Global.IdeleAbsoluteValue

namespace Langlands.Global.AdelicGL

variable (F : Type uF) [Field F] [NumberField F]

/-- A one-by-one matrix is the scalar matrix of its determinant idele. -/
@[simp] theorem scalar_determinant_one (g : AdelicGL F 1) :
    scalar F 1 (determinant F 1 g) = g := by
  apply Units.ext
  ext i j
  fin_cases i
  fin_cases j
  change Matrix.det (g : Matrix (Fin 1) (Fin 1) (Adeles F)) = _
  exact Matrix.det_fin_one _

/-- A closed positive determinant band has compact rational-left covering in rank one. -/
theorem exists_isCompact_determinantBandCover (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ K : Set (AdelicGL F 1), IsCompact K ∧
      ∀ x : AdelicGL F 1,
        lo ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F 1 x : ℝ≥0) : ℝ) ∧
          ((AdelicBlockDeterminantCharacter.determinantNorm F 1 x : ℝ≥0) : ℝ) ≤ hi →
            ∃ a : RationalGL F 1, rational F 1 a * x ∈ K := by
  obtain ⟨C, hC, hcover⟩ := IdeleAbsoluteValue.exists_isCompact_bandCover F lo hi hlo
  refine ⟨scalar F 1 '' C, hC.image (scalar F 1).continuous, ?_⟩
  intro x hx
  obtain ⟨a, ha⟩ := hcover (determinant F 1 x) hx
  refine ⟨Matrix.GeneralLinearGroup.scalar (Fin 1) a,
    ⟨diagonalUnits F a * determinant F 1 x, ha, ?_⟩⟩
  rw [map_mul, scalar_determinant_one]
  congr 1
  change Matrix.GeneralLinearGroup.scalar (Fin 1) (diagonalUnits F a) =
    Matrix.GeneralLinearGroup.map (algebraMap F (Adeles F))
      (Matrix.GeneralLinearGroup.scalar (Fin 1) a)
  rw [Matrix.GeneralLinearGroup.map_scalar]
  rfl

end Langlands.Global.AdelicGL

namespace Langlands.Automorphic.OperatorDeterminantSlice

open Langlands.Global ContinuousRationalFunctions MeasureTheory NumberField
open scoped NNReal

variable (F : Type uF) [Field F] [NumberField F]

local instance : T2Space (AdelicGL F 1) := by
  let := Langlands.GroupScheme.GeneralLinear.isAffine_groupScheme (Fin 1) (CommRingCat.of F)
  exact (GeneralLinearGroupPoints.adelicHomeomorph F 1).toHomeomorph.t2Space

variable [MeasurableSpace (AdelicGL F 1)] [BorelSpace (AdelicGL F 1)]

/-- Every continuous matrix function has finite squared integral on a compact set. -/
theorem lintegral_enorm_sq_lt_top_of_isCompact (measure : Measure (AdelicGL F 1))
    [IsFiniteMeasureOnCompacts measure] {K : Set (AdelicGL F 1)} (hK : IsCompact K)
    (f : C(AdelicGL F 1, ℂ)) :
    (∫⁻ x in K, ‖f x‖ₑ ^ 2 ∂measure) < ⊤ := by
  have hi : IntegrableOn (fun x => ‖f x‖ ^ 2) K measure :=
    ((f.continuous.norm.pow 2).continuousOn).integrableOn_compact hK
  simpa only [hasFiniteIntegral_iff_enorm, enorm_pow, enorm_norm] using hi.hasFiniteIntegral

/-- The rank-one covering estimate follows from compactness and continuity alone. -/
theorem exists_rankOne_cover_finite (measure : Measure (AdelicGL F 1))
    [IsFiniteMeasureOnCompacts measure] (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ K : Set (AdelicGL F 1), MeasurableSet K ∧
      (∀ x : AdelicGL F 1,
        lo ≤ ((AdelicBlockDeterminantCharacter.determinantNorm F 1 x : ℝ≥0) : ℝ) ∧
          ((AdelicBlockDeterminantCharacter.determinantNorm F 1 x : ℝ≥0) : ℝ) ≤ hi →
            ∃ a : RationalGL F 1, AdelicGL.rational F 1 a * x ∈ K) ∧
      (∀ f : C(AdelicGL F 1, ℂ), (∫⁻ x in K, ‖f x‖ₑ ^ 2 ∂measure) < ⊤) := by
  obtain ⟨K, hK, hcover⟩ := AdelicGL.exists_isCompact_determinantBandCover F lo hi hlo
  exact ⟨K, hK.measurableSet, hcover,
    fun f => lintegral_enorm_sq_lt_top_of_isCompact F measure hK f⟩

variable (S : OperatorRealization F 1)
local instance : AddCommGroup (RationalInvariantFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F 1) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F 1) := Submodule.addCommGroup _
local instance : AddCommGroup S.Space := Submodule.addCommGroup _

/-- In rank one the original finite action has a positive form for a unitary central character. -/
def rankOneFiniteInvariantPositiveForm
    (χ : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (hχ : ∀ x, ‖(χ x : ℂ)‖ = 1) (hS : S.HasCentralCharacter χ) :
    Langlands.InvariantPositiveForm S.finiteRepresentation := by
  let h := exists_rankOne_cover_finite F (matrixHaarMeasure F 1) 1 2 (by norm_num)
  let K := Classical.choose h
  have hK := Classical.choose_spec h
  exact finiteInvariantPositiveFormOfCover F 1 S (by norm_num) χ hχ hS K hK.1 hK.2.1
    (fun f => hK.2.2 ⟨evaluate F 1 (S.toContinuous f), continuous_evaluate F 1 (S.toContinuous f)⟩)

end Langlands.Automorphic.OperatorDeterminantSlice
