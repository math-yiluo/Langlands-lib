import Langlands.Global.RankinSelberg.ComplexOpenBruhatCoordinates
import Langlands.Global.RankinSelberg.ComplexBruhatRestriction
import Langlands.Global.RankinSelberg.ComplexJacquetChamberIntertwiner
import Langlands.HarmonicAnalysis.Distribution.SmoothRightInvariantHaar

/-! # Multiplicity one for finite-order complex Whittaker functionals -/

noncomputable section

open Set TopologicalSpace MeasureTheory
open scoped Classical ContDiff Distributions Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerMultiplicityOne

open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter complexStandardMeasure)
open Langlands.HarmonicAnalysis (UnitaryAdditiveCharacter smoothRightInvariantHaar)
open ComplexOppositeCompactChart (Coordinates)
open ComplexBruhatTestExtension (ChartTest extendTest)
open ComplexBruhatChartDistribution (complexBruhatChartDistribution)
open ComplexBruhatRestriction (complexBruhatRestriction)
open ComplexOpenBruhatCoordinates (openCoordinates contDiff_openCoordinates_mul contDiff_openCoordinates_inv
  contDiff_openWhittakerCharacter smoothTranslate_extendTest_long)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile)
open ComplexWhittakerTranslateExtension (smoothTranslate)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_isHaar)
open ComplexJacquetChamberIntertwiner (entryHaar_isMulRightInvariant)

attribute [local instance] ArchimedeanLocal.archimedeanComplexNMeasurable ArchimedeanLocal.archimedeanComplexNBorel

local notation "G" => fun r => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => fun r => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "V" => fun r ds => SmoothStandard (r + 1) ds
local notation "E" => fun r => Coordinates (r + 1)

variable {r : ℕ} {ds : List ComplexCharacterData}

/-- Exact right Whittaker covariance on the smooth standard module, with a finite
compact difference bound. -/
def IsFiniteOrderWhittakerFunctional (a : ℂˣ) (L : V r ds →ₗ[ℂ] ℂ) : Prop :=
  ∃ (J : ℕ) (C : ℝ), 0 ≤ C ∧
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) ∧
    ∀ (F : V r ds) (u : G r), u ∈ N r →
      L (smoothTranslate u F) = complexWhittakerCharacter a u * L F

private def multiplyTest {b : E r → ℂ} (hb : ContDiff ℝ ∞ b) :
    ChartTest (r + 1) →L[ℂ] ChartTest (r + 1) :=
  TestFunction.limitCLM ℂ
    (fun f => ⟨fun z => f z * b z, f.contDiff.mul hb, f.hasCompactSupport.mul_right,
      tsupport_mul_subset_left.trans f.tsupport_subset⟩)
    (fun _ hK => (TestFunction.ofSupportedInCLM ℂ hK).comp
      (ContDiffMapSupportedIn.bilinLeftCLM (ContinuousLinearMap.mul ℂ ℂ) hb))
    (fun _ _ _ => rfl)

@[simp] private theorem multiplyTest_apply {b : E r → ℂ} (hb : ContDiff ℝ ∞ b) (f : ChartTest (r + 1))
    (z : E r) : multiplyTest hb f z = f z * b z := rfl

private theorem whittakerCharacter_ne_zero (a : ℂˣ) (g : G r) : complexWhittakerCharacter a g ≠ 0 := by
  have h : ‖complexWhittakerCharacter a g‖ = 1 :=
    UnitaryAdditiveCharacter.norm_complex (complexScaledCharacter a) _
  intro hz
  rw [hz, norm_zero] at h
  exact zero_ne_one h

private theorem whittakerCharacter_mul (a : ℂˣ) (u v : N r) :
    complexWhittakerCharacter a (u * v).val =
      complexWhittakerCharacter a u.val * complexWhittakerCharacter a v.val := by
  simp only [complexWhittakerCharacter, Langlands.GeneralLinear.UpperUnipotent.mul_adjacent_entry,
    Finset.sum_add_distrib, AddChar.map_add_eq_mul]

private def openCharacter (a : ℂˣ) (z : E r) : ℂ :=
  complexWhittakerCharacter a ((openCoordinates r).symm z).val

private def openHaar (r : ℕ) : Measure (E r) :=
  (entryHaar complexStandardMeasure (r + 1)).map (openCoordinates r)

/-- The restriction of a finite-order Whittaker functional to the open cell is a
scalar multiple of Haar integration twisted by the inverse unipotent character. -/
theorem exists_openWhittaker_coefficient (a : ℂˣ) (L : V r ds →ₗ[ℂ] ℂ)
    (hL : IsFiniteOrderWhittakerFunctional a L) :
    ∃ c : ℂ, ∀ φ : ChartTest (r + 1), L (extendTest Fin.revPerm ds φ) =
      c * (∫ z, φ z * (openCharacter a z)⁻¹ ∂openHaar r) := by
  obtain ⟨J, C, hC, hBound, hCov⟩ := hL
  obtain ⟨T, hT⟩ := complexBruhatChartDistribution (r + 1) ds Fin.revPerm L J C hC hBound
  let e := openCoordinates r
  let χ : E r → ℂ := openCharacter a
  have hχ : ContDiff ℝ ∞ χ := contDiff_openWhittakerCharacter a
  have hne (z : E r) : χ z ≠ 0 := whittakerCharacter_ne_zero a (e.symm z).val
  let M := multiplyTest hχ
  let T' := T.comp M
  have hT' (u : N r) (f f' : ChartTest (r + 1))
      (hf' : ∀ z, f' z = f (e (e.symm z * u))) : T' f' = T' f := by
    let c := complexWhittakerCharacter a u.val
    have hTest (z : E r) : (c • M f') z = M f (e (e.symm z * u)) := by
      change c * multiplyTest hχ f' z = multiplyTest hχ f (e (e.symm z * u))
      rw [multiplyTest_apply, multiplyTest_apply, hf']
      have hm : χ (e (e.symm z * u)) = χ z * c := by
        change complexWhittakerCharacter a (e.symm (e (e.symm z * u))).val = _
        rw [e.symm_apply_apply, whittakerCharacter_mul]
        rfl
      rw [hm]
      ring
    have he : T (c • M f') = c * T (M f) := by
      rw [hT, smoothTranslate_extendTest_long ds u (M f) (c • M f') hTest,
        hCov _ u.val u.2, ← hT]
    rw [map_smul, smul_eq_mul] at he
    exact mul_left_cancel₀ (whittakerCharacter_ne_zero a u.val) he
  let μ := entryHaar complexStandardMeasure (r + 1)
  let : μ.IsHaarMeasure := entryHaar_isHaar complexStandardMeasure (r + 1)
  let : μ.IsMulRightInvariant := entryHaar_isMulRightInvariant complexStandardMeasure r
  obtain ⟨c, hc⟩ := smoothRightInvariantHaar e μ
    (contDiff_openCoordinates_mul r) (contDiff_openCoordinates_inv r) T' hT'
  have hInv : ContDiff ℝ ∞ (fun z => (χ z)⁻¹) := hχ.inv hne
  refine ⟨c, fun φ => ?_⟩
  let g := multiplyTest hInv φ
  have hEq : M g = φ := by
    ext z
    change multiplyTest hχ (multiplyTest hInv φ) z = φ z
    rw [multiplyTest_apply, multiplyTest_apply, mul_assoc, inv_mul_cancel₀ (hne z), mul_one]
  have h := hc g
  change T (M g) = c * (∫ z, g z ∂openHaar r) at h
  rw [hEq, hT] at h
  exact h

/-- Every finite-order smooth Whittaker functional is proportional to any given
nonzero finite-order smooth Whittaker functional for the same data. -/
def ComplexSmoothWhittakerMultiplicityOneStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ) (L L₀ : V r ds →ₗ[ℂ] ℂ),
    IsFiniteOrderWhittakerFunctional a L → IsFiniteOrderWhittakerFunctional a L₀ →
    L₀ ≠ 0 → ∃ c : ℂ, L = c • L₀

set_option maxHeartbeats 1050000 in
theorem complexSmoothWhittakerMultiplicityOne : ComplexSmoothWhittakerMultiplicityOneStatement := by
  intro r ds a L L₀ hL hL₀ hNonzero
  obtain ⟨c, hc⟩ := exists_openWhittaker_coefficient a L hL
  obtain ⟨c₀, hc₀⟩ := exists_openWhittaker_coefficient a L₀ hL₀
  obtain ⟨J, C, hC, hBound, hCov⟩ := hL
  obtain ⟨J₀, C₀, hC₀, hBound₀, hCov₀⟩ := hL₀
  have hcnz : c₀ ≠ 0 := fun h => hNonzero
    (complexBruhatRestriction r ds a L₀ J₀ C₀ hC₀ hBound₀ hCov₀ (fun φ => by rw [hc₀, h, zero_mul]))
  let b := c / c₀
  let D := L - b • L₀
  have hBoundD (F : V r ds) (R : ℝ)
      (hR : CompactProfileDifferenceBound (max J J₀) (compactProfile F) R) :
      ‖D F‖ ≤ (C + ‖b‖ * C₀) * R := by
    have h1 := hBound F R (fun ks hks => hR ks (hks.trans (le_max_left _ _)))
    have h2 := hBound₀ F R (fun ks hks => hR ks (hks.trans (le_max_right _ _)))
    change ‖L F - b * L₀ F‖ ≤ _
    calc
      ‖L F - b * L₀ F‖ ≤ ‖L F‖ + ‖b * L₀ F‖ := norm_sub_le _ _
      _ ≤ C * R + ‖b‖ * (C₀ * R) := by
        rw [norm_mul]
        exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 (norm_nonneg _))
      _ = (C + ‖b‖ * C₀) * R := by ring
  have hCovD (F : V r ds) (u : G r) (hu : u ∈ N r) :
      D (smoothTranslate u F) = complexWhittakerCharacter a u * D F := by
    change L (smoothTranslate u F) - b * L₀ (smoothTranslate u F) =
      complexWhittakerCharacter a u * (L F - b * L₀ F)
    rw [hCov F u hu, hCov₀ F u hu]
    ring
  have hVan (φ : ChartTest (r + 1)) : D (extendTest Fin.revPerm ds φ) = 0 := by
    change L (extendTest Fin.revPerm ds φ) - b * L₀ (extendTest Fin.revPerm ds φ) = 0
    rw [hc, hc₀]
    dsimp only [b]
    field_simp [hcnz]
    ring
  have hD := complexBruhatRestriction r ds a D (max J J₀) (C + ‖b‖ * C₀)
    (add_nonneg hC (mul_nonneg (norm_nonneg _) hC₀)) hBoundD hCovD hVan
  exact ⟨b, sub_eq_zero.mp hD⟩

end Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerMultiplicityOne
