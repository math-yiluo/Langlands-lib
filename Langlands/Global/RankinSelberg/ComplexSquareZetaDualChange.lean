import Langlands.Global.RankinSelberg.ComplexSquareZetaProductTate
import Langlands.Representation.Archimedean.ComplexPermutationSwap
import Langlands.Representation.Archimedean.ComplexReverseTwist

/-! # Changes of variables for the dual square zeta integral

Left multiplication by the longest Weyl matrix preserves the dual integral and
its absolute integrability. The inducing characters are inverted in reverse order. -/

noncomputable section

open Matrix MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta

open Langlands.Archimedean Langlands.Archimedean.ComplexReverseTwist
open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexGodement (normPower upperTriangularEntries)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance squareDualGLMeasurable (n : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear n ℂ) := borel _
local instance squareDualGLBorel (n : ℕ) :
    BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Mat" => Matrix (Fin n) (Fin n) ℂ
local notation "Z" => Fin n → ℂ
local notation "X" => UpperEntryPair n → ℂ

private def leftWeylEquiv : Mat ≃L[ℝ] Mat :=
  let L := ContinuousLinearMap.mul ℝ Mat (w0Mat n)
  (LinearEquiv.ofInvolutive L.toLinearMap fun M => by
    change w0Mat n * (w0Mat n * M) = M
    rw [← mul_assoc, w0Mat_mul_self, one_mul]).toContinuousLinearEquiv

/-- Left translation of a square Schwartz test by the longest Weyl element. -/
def leftWeylTest (Φ : 𝓢(Mat, ℂ)) : 𝓢(Mat, ℂ) :=
  SchwartzMap.compCLMOfContinuousLinearEquiv ℂ leftWeylEquiv Φ

theorem leftWeylTest_apply (Φ : 𝓢(Mat, ℂ)) (M : Mat) :
    leftWeylTest Φ M = Φ (w0Mat n * M) := rfl

/-- The inverse-transpose twist with the longest Weyl element has reversed inverse data
in the upper-Borel standard module. -/
theorem twistLin_mem_standard_ofFn (ds : Fin n → ComplexCharacterData) {f : G → ℂ}
    (hf : f ∈ complexStandardModule n (List.ofFn ds)) :
    twistLin n f ∈ complexStandardModule n (List.ofFn fun j => (ds j.rev).inv) := by
  refine twistLin_mem_principalSeries (χ := complexPositionCharacter (List.ofFn ds)) ?_ hf
  intro j z
  have hj : (j : ℕ) < (List.ofFn fun j => (ds j.rev).inv).length := by simp
  have hj' : (j.rev : ℕ) < (List.ofFn ds).length := by
    rw [List.length_ofFn]
    exact j.rev.isLt
  rw [ComplexPermutation.complexPositionCharacter_eq_get _ _ hj,
    ComplexPermutation.complexPositionCharacter_eq_get _ _ hj']
  simp only [List.get_eq_getElem, List.getElem_ofFn, ComplexCharacterData.inv_character_apply,
    map_inv, Units.val_inv_eq_inv_val]

private theorem dualKernel_comp_leftWeyl (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (s : ℂ) :
    (zetaKernel Φ (fun g => f (inverseTranspose n ℂ g)) s) ∘ (w0GL n * ·) =
      zetaKernel (leftWeylTest Φ) (twistLin n f) s := by
  have hW (p : ℂ) : normPower p (determinant (w0GL n)) = 1 := by
    change (ComplexMaximalParabolicIntegration.normSqC (w0Mat n).det) ^ p = 1
    have h := ComplexMaximalParabolicIntegration.normSqC_det_unitary
      (⟨w0GL n, w0GL_mem⟩ : K)
    change ComplexMaximalParabolicIntegration.normSqC (w0Mat n).det = 1 at h
    rw [h, Complex.one_cpow]
  have hι (g : G) : inverseTranspose n ℂ g = conjAut g := Units.ext rfl
  funext g
  simp only [Function.comp_apply, zetaKernel, leftWeylTest_apply, twistLin_apply,
    ComplexReverseTwist.twist, Units.val_mul, w0GL_val, hι, map_mul, conjAut_w0GL, hW, one_mul]

/-- The change `g ↦ w₀g` moves the dual transpose-inverse zeta kernel to the upper-Borel
standard vector given by the twist, preserving the integral and absolute integrability. -/
def ComplexSquareZetaDualChangeStatement : Prop :=
  ∀ (μ : Measure G) [μ.IsMulLeftInvariant] (Φ : 𝓢(Mat, ℂ)) (f : G → ℂ) (s : ℂ),
    (Integrable (zetaKernel Φ (fun g => f (inverseTranspose n ℂ g)) s) μ ↔
      Integrable (zetaKernel (leftWeylTest Φ) (twistLin n f) s) μ) ∧
    (∫ g, zetaKernel Φ (fun g => f (inverseTranspose n ℂ g)) s g ∂μ) =
      ∫ g, zetaKernel (leftWeylTest Φ) (twistLin n f) s g ∂μ

theorem complexSquareZetaDualChange : ComplexSquareZetaDualChangeStatement (n := n) := by
  intro μ hμ Φ f s
  rw [← dualKernel_comp_leftWeyl Φ f s]
  refine ⟨((measurePreserving_mul_left μ (w0GL n)).integrable_comp_emb
    (measurableEmbedding_mulLeft _)).symm, ?_⟩
  exact (integral_mul_left_eq_self (μ := μ)
    (zetaKernel Φ (fun g => f (inverseTranspose n ℂ g)) s) (w0GL n)).symm

/-- The permutation of strictly upper entries induced by transposition and reversing both axes. -/
def reverseOff (n : ℕ) : Equiv.Perm (UpperEntryPair n) :=
  Function.Involutive.toPerm (fun ij => ⟨(ij.1.2.rev, ij.1.1.rev), Fin.rev_lt_rev.mpr ij.2⟩)
    (fun ij => Subtype.ext (by simp))

theorem reverseOff_apply_val (ij : UpperEntryPair n) :
    (reverseOff n ij).1 = (ij.1.2.rev, ij.1.1.rev) := rfl

theorem measurePreserving_reverseOff (ν : Measure ℂ) [SigmaFinite ν] :
    MeasurePreserving (fun z : X => z ∘ reverseOff n) (Measure.pi fun _ => ν)
      (Measure.pi fun _ => ν) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : UpperEntryPair n => ℂ) (reverseOff n).symm
  have he : (e : X → X) = fun z => z ∘ reverseOff n := by
    funext z ij
    calc
      e z ij = e z ((reverseOff n).symm (reverseOff n ij)) :=
        congrArg (e z) ((reverseOff n).symm_apply_apply ij).symm
      _ = z (reverseOff n ij) :=
        MeasurableEquiv.piCongrLeft_apply_apply (β := fun _ => ℂ)
          (reverseOff n).symm z (reverseOff n ij)
  rw [← he]
  exact measurePreserving_piCongrLeft (fun _ => ν) (reverseOff n).symm

/-- Weyl conjugation of an upper triangular matrix produces the transpose of the triangular
matrix with reverse diagonal and reindexed upper entries. -/
theorem w0_conjugate_triangular (d : Z) (z : X) :
    w0Mat n * upperTriangularEntries d z * w0Mat n =
      (upperTriangularEntries (d ∘ Fin.rev) (z ∘ reverseOff n))ᵀ := by
  ext i j
  rw [w0Mat_mul_mul_w0Mat_apply, Matrix.transpose_apply]
  by_cases hji : j < i
  · have hrev : i.rev < j.rev := Fin.rev_lt_rev.mpr hji
    simp only [upperTriangularEntries, dite_eq_left hrev, dite_eq_left hji, Function.comp_apply]
    rfl
  · have hrev : ¬ i.rev < j.rev := fun h => hji (Fin.rev_lt_rev.mp h)
    simp only [upperTriangularEntries, dite_eq_right hrev, dite_eq_right hji, Function.comp_apply]
    by_cases hij : i = j
    · subst j
      simp
    · simp [Ne.symm hij, Fin.rev_injective.ne hij]

private def shiftedConj (k : K) : K := (⟨w0GL n, w0GL_mem⟩ : K) * conjK n k

private theorem shiftedConj_val (k : K) :
    (shiftedConj k).val = ComplexReverseTwist.twist k.val := rfl

private theorem measurePreserving_shiftedConj (κ : Measure K) [κ.IsHaarMeasure] :
    MeasurePreserving (shiftedConj (n := n)) κ κ :=
  (measurePreserving_mul_left κ (⟨w0GL n, w0GL_mem⟩ : K)).comp
    (MonoidHom.measurePreserving continuous_conjK surjective_conjK rfl)

/-- In the compact average of the twisted vector, change the unitary variable by
`k ↦ w₀(kᵀ)⁻¹`. The resulting weight is the original compact restriction. -/
theorem rightAverage_dual_change (κ : Measure K) [IsFiniteMeasure κ] [κ.IsHaarMeasure]
    (Φ : 𝓢(Mat, ℂ)) {f : G → ℂ} (hf : Continuous f) (M : Mat) :
    rightAverage κ (fun k => twistLin n f k.val)
        ((hf.comp continuous_twist).comp continuous_subtype_val) (leftWeylTest Φ) M =
      ∫ k : K, f k.val * Φ ((w0Mat n * M * w0Mat n) * (conjK n k).val.val) ∂κ := by
  rw [rightAverage_apply]
  let I (k : K) := twistLin n f k.val * leftWeylTest Φ (M * k.val.val)
  have hI : Continuous I := (hf.comp (continuous_twist.comp continuous_subtype_val)).mul
    ((leftWeylTest Φ).continuous.comp
      (continuous_const.matrix_mul (Units.continuous_val.comp continuous_subtype_val)))
  have hκ := measurePreserving_shiftedConj (n := n) κ
  change ∫ k, I k ∂κ = _
  rw [← hκ.map_eq, integral_map hκ.measurable.aemeasurable hI.aestronglyMeasurable, hκ.map_eq]
  congr 1
  funext k
  have htw : twistLin n f (shiftedConj k).val = f k.val := by
    rw [twistLin_apply, shiftedConj_val, ComplexReverseTwist.twist_twist]
  change twistLin n f (shiftedConj k).val * leftWeylTest Φ (M * (shiftedConj k).val.val) = _
  rw [htw, leftWeylTest_apply]
  change f k.val * Φ (w0Mat n * (M * (w0Mat n * (conjK n k).val.val))) = _
  simp only [mul_assoc]

end Langlands.Global.RankinSelbergGlobal.ComplexSquareZeta
