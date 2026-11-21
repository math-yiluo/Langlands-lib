import Langlands.Global.RankinSelberg.ComplexWhittakerSmoothExtension
import Langlands.Representation.Archimedean.ComplexStandardBorelTestMap

/-! # Compact profile bounds for complex Borel averages -/

noncomputable section

open Filter Function MeasureTheory Set TopologicalSpace
open scoped ContDiff Distributions Matrix Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexCompactSmoothDifferences
  (CompactMatrixJetBound CompactProfileDifferenceBound compactFunctionDifference
    complexCompactSmoothDifferences)
open ComplexCompactDifferences (displacementProduct)
open ComplexWhittakerSmoothExtension (compactProfile)

namespace ComplexBorelProfile

variable (n : ℕ)

local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ

private def adjointCLM : Mat →L[ℝ] Mat :=
  ({ toFun M := Mᴴ
     map_add' M N := Matrix.conjTranspose_add M N
     map_smul' r M := Matrix.conjTranspose_smul r M } : Mat →ₗ[ℝ] Mat).toContinuousLinearMap

private def rightAdjointCLM (b : Mat) : Mat →L[ℝ] Mat :=
  ((ContinuousLinearMap.mul ℝ Mat).flip b).comp (adjointCLM n)

private theorem rightAdjointCLM_apply (b x : Mat) :
    rightAdjointCLM n b x = xᴴ * b :=
  rfl

private theorem norm_rightAdjointCLM_le (b : Mat) :
    ‖rightAdjointCLM n b‖ ≤ ‖adjointCLM n‖ * ‖b‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  change ‖adjointCLM n x * b‖ ≤ _
  calc
    _ ≤ ‖adjointCLM n x‖ * ‖b‖ := norm_mul_le _ _
    _ ≤ (‖adjointCLM n‖ * ‖x‖) * ‖b‖ :=
      mul_le_mul_of_nonneg_right ((adjointCLM n).le_opNorm x) (norm_nonneg _)
    _ = _ := by ring

private theorem derivative_comp_bound {K : Compacts Mat} (f : 𝓓_{K}(Mat, ℂ))
    (J : ℕ) (b : Mat) {R : ℝ} (hR : 1 ≤ R) (hb : ‖rightAdjointCLM n b‖ ≤ R) :
    CompactMatrixJetBound J (f ∘ rightAdjointCLM n b)
      (ContDiffMapSupportedIn.supSeminorm ℂ Mat ℂ ⊤ K J f * R ^ J) := by
  intro i hi x _
  let A := rightAdjointCLM n b
  rw [A.iteratedFDeriv_comp_right f.contDiff x (by simp)]
  have hSrc := ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℂ
    (i := i) (f := f) (x := A x)
  have hSemi : N[ℂ]_{K, i} f ≤ ContDiffMapSupportedIn.supSeminorm ℂ Mat ℂ ⊤ K J f := by
    exact (Finset.le_sup (f := ContDiffMapSupportedIn.seminorm ℂ Mat ℂ ⊤ K)
      (Finset.mem_Iic.mpr hi) : _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ Mat ℂ ⊤ K J) f
  calc
    _ ≤ ‖iteratedFDeriv ℝ i f (A x)‖ * ‖A‖ ^ i := by
      simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
        (iteratedFDeriv ℝ i f (A x)).norm_compContinuousLinearMap_le (fun _ : Fin i => A)
    _ ≤ ContDiffMapSupportedIn.supSeminorm ℂ Mat ℂ ⊤ K J f * R ^ J := by
      gcongr
      · exact hSrc.trans hSemi
      · exact (pow_le_pow_left₀ (norm_nonneg _) hb _).trans (pow_le_pow_right₀ hR hi)

private theorem compactDifference_zero (ks : List U) (k : U) :
    compactFunctionDifference ks (0 : U → ℂ) k = 0 := by
  induction ks generalizing k with
  | nil => rfl
  | cons u ks ih =>
    change compactFunctionDifference ks 0 (k * u) - compactFunctionDifference ks 0 k = 0
    rw [ih, ih, sub_self]

private theorem compactDifference_integral {Y : Type*} [MeasurableSpace Y] (μ : Measure Y)
    (η : Y → ℂ) (H : Y → U → ℂ) (hInt : ∀ k : U, Integrable (fun b => η b * H b k) μ)
    (ks : List U) (k : U) :
    Integrable (fun b => η b * compactFunctionDifference ks (H b) k) μ ∧
    compactFunctionDifference ks (fun k => ∫ b, η b * H b k ∂μ) k =
      ∫ b, η b * compactFunctionDifference ks (H b) k ∂μ := by
  induction ks generalizing k with
  | nil => exact ⟨hInt k, rfl⟩
  | cons u ks ih =>
    have h₁ := ih (k * u)
    have h₂ := ih k
    refine ⟨?_, ?_⟩
    · refine (h₁.1.sub h₂.1).congr (Eventually.of_forall fun b => ?_)
      change η b * compactFunctionDifference ks (H b) (k * u) -
          η b * compactFunctionDifference ks (H b) k =
        η b * (compactFunctionDifference ks (H b) (k * u) - compactFunctionDifference ks (H b) k)
      rw [mul_sub]
    · change compactFunctionDifference ks (fun k => ∫ b, η b * H b k ∂μ) (k * u) -
          compactFunctionDifference ks (fun k => ∫ b, η b * H b k ∂μ) k =
        ∫ b, η b * (compactFunctionDifference ks (H b) (k * u) -
          compactFunctionDifference ks (H b) k) ∂μ
      rw [h₁.2, h₂.2]
      simp only [mul_sub, integral_sub h₁.1 h₂.1]

end ComplexBorelProfile

open ComplexBorelProfile

local notation "Mat" n => Matrix (Fin n) (Fin n) ℂ
local notation "Borel" n => upperTriangularSubgroup n ℂ
local notation "GL" n => Langlands.GeneralLinear n ℂ
local notation "U" n => Matrix.unitaryGroup (Fin n) ℂ

/-- On each fixed compact support, one source derivative seminorm
controls the compact profile of Borel averages through the prescribed order. -/
def ComplexBorelProfileBoundStatement : Prop :=
  ∀ (n : ℕ) [SecondCountableTopology (Borel n)] [MeasurableSpace (Borel n)] [BorelSpace (Borel n)]
    (μ : Measure (Borel n)) [μ.IsHaarMeasure] (ds : List ComplexCharacterData)
    (J : ℕ) (K : Compacts (Mat n)) (hK : (K : Set (Mat n)) ⊆ matrixUnitsOpen ℂ n),
    ∃ A : ℝ, 0 ≤ A ∧ ∀ f : 𝓓_{K}(Mat n, ℂ),
      CompactProfileDifferenceBound J (compactProfile
        (complexStandardBorelTestMap n ds μ (TestFunction.ofSupportedIn hK f)))
        (A * ContDiffMapSupportedIn.supSeminorm ℂ (Mat n) ℂ ⊤ K J f)

theorem complexBorelProfileBound : ComplexBorelProfileBoundStatement := by
  intro n _ _ _ μ _ ds J K hK
  let η := complexStandardBorelCharacter n ds
  let Ku : Set (Mat n) := (Units.val : (GL n) → Mat n) '' (unitaryCompact ℂ n : Set (GL n))
  have hKu : IsCompact Ku := (ComplexDuality.isCompact_unitaryCompact n).image Units.continuous_val
  have hKuΩ : Ku ⊆ matrixUnitsOpen ℂ n := by
    rintro _ ⟨g, _, rfl⟩
    exact Units.isUnit g
  obtain ⟨S, hS, hTransport⟩ :=
    exists_compact_complexBorel_right_transport n hKu K.isCompact hKuΩ hK
  have hval : Continuous (fun b : Borel n => b.val.val) :=
    Units.continuous_val.comp continuous_subtype_val
  have hη := continuous_complexStandardBorelCharacter n ds
  obtain ⟨B, hB⟩ := (hS.image hval.norm).bddAbove
  obtain ⟨E, hE⟩ := (hS.image hη.norm).bddAbove
  let R := max 1 (‖adjointCLM n‖ * max 0 B)
  let L := max 0 E
  have hR : 1 ≤ R := le_max_left _ _
  have hnorm (b : Borel n) (hb : b ∈ S) : ‖rightAdjointCLM n b.val.val‖ ≤ R :=
    (norm_rightAdjointCLM_le n _).trans
      ((mul_le_mul_of_nonneg_left ((hB (mem_image_of_mem _ hb)).trans (le_max_right _ _))
        (norm_nonneg _)).trans (le_max_right _ _))
  obtain ⟨C, hC, hDiff⟩ := complexCompactSmoothDifferences n J
  refine ⟨L * C * R ^ J * μ.real S, by positivity, fun f ks hks k => ?_⟩
  let f' := TestFunction.ofSupportedIn hK f
  let p := ContDiffMapSupportedIn.supSeminorm ℂ (Mat n) ℂ ⊤ K J f
  let H (b : Borel n) (k : U n) := f ((Unitary.toUnits k)⁻¹.val * b.val.val)
  have hInt (k : U n) : Integrable (fun b => η b * H b k) μ :=
    integrable_complexBorelMatrixAverage n μ η hη f' (hx := Units.isUnit (Unitary.toUnits k)⁻¹)
  have hHB (b : Borel n) (hb : b ∈ S) :
      CompactProfileDifferenceBound J (H b) (C * (p * R ^ J)) := by
    let V := rightAdjointCLM n b.val.val
    have hcomp : ContDiff ℝ ∞ (f ∘ V) := f.contDiff.comp V.contDiff
    have heq : (fun k : U n => (f ∘ V) k.val) = H b := by
      funext k
      change f (rightAdjointCLM n b.val.val k.val) = _
      rw [rightAdjointCLM_apply]
      rfl
    rw [← heq]
    exact hDiff (f ∘ V) (p * R ^ J) hcomp (by positivity) (derivative_comp_bound n f J _ hR (hnorm b hb))
  have hzero (b : Borel n) (hb : b ∉ S) : H b = 0 := by
    funext k
    have hk : (Unitary.toUnits k)⁻¹.val ∈ Ku :=
      ⟨(Unitary.toUnits k)⁻¹, (unitaryCompact ℂ n).inv_mem k.property, rfl⟩
    have hx : (Unitary.toUnits k)⁻¹.val * b.val.val ∉ K :=
      fun hx => hb (hTransport b _ hk hx)
    exact f.zero_on_compl hx
  change ‖compactFunctionDifference ks (fun k => ∫ b, η b * H b k ∂μ) k‖ ≤ _
  rw [(compactDifference_integral n μ η H hInt ks k).2,
    ← setIntegral_eq_integral_of_forall_compl_eq_zero (s := S) (fun b hb => by
      rw [hzero b hb, compactDifference_zero, mul_zero])]
  calc
    _ ≤ (L * (C * (p * R ^ J)) * displacementProduct ks) * μ.real S := by
      apply norm_setIntegral_le_of_norm_le_const hS.measure_lt_top
      intro b hb
      rw [norm_mul]
      calc
        _ ≤ L * ((C * (p * R ^ J)) * displacementProduct ks) :=
          mul_le_mul ((hE (mem_image_of_mem _ hb)).trans (le_max_right _ _))
            (hHB b hb ks hks k) (norm_nonneg _) (le_max_left _ _)
        _ = _ := by ring
    _ = _ := by ring

end Langlands.Global.RankinSelbergGlobal
