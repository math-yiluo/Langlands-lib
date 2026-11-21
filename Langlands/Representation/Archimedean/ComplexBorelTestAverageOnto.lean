import Langlands.Representation.Archimedean.ComplexBorelTestAverage
import Langlands.Representation.GodementJacquet.ComplexTriangularHaar

/-! # Surjectivity of complex Borel averaging onto smooth induced sections -/

noncomputable section

open Function Filter Set TopologicalSpace MeasureTheory
open scoped ContDiff Distributions Manifold Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Archimedean

open Langlands.GeneralLinear
open Langlands.GodementJacquet (complexTriangularCoordinates complexTriangularCoordinates_apply)

local notation "Mat" n => Matrix (Fin n) (Fin n) ℂ
local notation "GL" n => Langlands.GeneralLinear n ℂ
local notation "Borel" n => upperTriangularSubgroup n ℂ

/-- Every smooth left Borel-equivariant section is the inverse-argument
weighted average of an actual compactly supported matrix test. -/
def ComplexBorelTestAverageOntoStatement : Prop :=
  ∀ (n : ℕ) [SecondCountableTopology (Borel n)] [MeasurableSpace (Borel n)] [BorelSpace (Borel n)]
    (μ : Measure (Borel n)) [μ.IsHaarMeasure] (η : (Borel n) →* ℂ),
  ∀ F : (GL n) → ℂ, ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ F →
    (∀ (b : Borel n) (g : GL n), F (b.val * g) = η b * F g) →
    ∃ f : 𝓓(matrixUnitsOpen ℂ n, ℂ),
      ∀ g : GL n, complexBorelMatrixAverage n μ η f g⁻¹.val = F g

namespace ComplexBorelTestAverageOnto

variable (n : ℕ)

private lemma exists_positive_unitary_test :
    ∃ (w : (Mat n) → ℝ) (ρ : 𝓓(matrixUnitsOpen ℂ n, ℂ)), (∀ x, ρ x = (w x : ℂ)) ∧
      (∀ x, 0 ≤ w x) ∧
      ∀ g : GL n, g ∈ unitaryCompact ℂ n → 0 < w g.val := by
  let K := (Units.val : (GL n) → Mat n) '' (unitaryCompact ℂ n : Set (GL n))
  have hK : IsCompact K := (ComplexDuality.isCompact_unitaryCompact n).image Units.continuous_val
  have hKΩ : K ⊆ matrixUnitsOpen ℂ n := by
    rintro _ ⟨g, -, rfl⟩
    exact Units.isUnit g
  obtain ⟨ε, hε, hεΩ⟩ := hK.exists_cthickening_subset_open (matrixUnitsOpen ℂ n).isOpen hKΩ
  obtain ⟨w, hwSupp, hw, hwRange⟩ :=
    (Metric.isOpen_thickening (δ := ε) (E := K)).exists_contDiff_support_eq
  have hwt : tsupport w ⊆ Metric.cthickening ε K := by
    rw [tsupport, hwSupp]
    exact Metric.closure_thickening_subset_cthickening _ _
  have hwc : HasCompactSupport w := hK.cthickening.of_isClosed_subset isClosed_closure hwt
  let ρ : 𝓓(matrixUnitsOpen ℂ n, ℂ) :=
    TestFunction.ofSupportedIn (K := ⟨tsupport w, hwc⟩) (hwt.trans hεΩ)
      (ContDiffMapSupportedIn.of_support_subset (Complex.ofRealCLM.contDiff.comp hw)
        (by
          intro x hx
          apply subset_tsupport w
          exact fun h => hx (by simp [h])))
  have hwNonneg (x : Mat n) : 0 ≤ w x := (hwRange (mem_range_self x)).1
  refine ⟨w, ρ, fun _ => rfl, hwNonneg, fun g hg => ?_⟩
  have hx : g.val ∈ support w := by
    rw [hwSupp]
    exact Metric.self_subset_thickening hε K ⟨g, hg, rfl⟩
  exact lt_of_le_of_ne (hwNonneg _) (mem_support.mp hx).symm

private theorem exists_borel_mul_unitary (g : GL n) :
    ∃ (b : Borel n) (k : GL n), k ∈ unitaryCompact ℂ n ∧ g = b.val * k := by
  obtain ⟨d, u, k, hk, rfl⟩ := ComplexDuality.exists_diagonalUnits_mul_upperUnipotent_mul_unitary g
  exact ⟨complexTriangularCoordinates n (d, u), k, hk, by
    rw [complexTriangularCoordinates_apply]
    rfl⟩

end ComplexBorelTestAverageOnto

open ComplexBorelTestAverageOnto

theorem complexBorelTestAverageOnto : ComplexBorelTestAverageOntoStatement := by
  intro n _ _ _ μ _ η F hF hCov
  obtain ⟨w, ρ, hρ, hw0, hwPos⟩ := exists_positive_unitary_test n
  let J (g : GL n) :=
    complexBorelMatrixAverage n μ (1 : (Borel n) →* ℂ) ρ g⁻¹.val
  have hJ_int (g : GL n) : J g = ∫ b : Borel n, ρ (g⁻¹.val * b.val.val) ∂μ := by
    simp only [J, complexBorelMatrixAverage, MonoidHom.one_apply, one_mul]
  have hJ_cov (b : Borel n) (g : GL n) : J (b.val * g) = J g := by
    simp only [J, complexBorelMatrixAverage_inv_mul, MonoidHom.one_apply, one_mul]
  have hJ_unitary (k : GL n) (hk : k ∈ unitaryCompact ℂ n) : J k ≠ 0 := by
    have hval : Continuous (fun b : Borel n => b.val.val) :=
      Units.continuous_val.comp continuous_subtype_val
    have hcts : Continuous (fun b : Borel n => w (k⁻¹.val * b.val.val)) := by
      rw [show (fun b : Borel n => w (k⁻¹.val * b.val.val)) =
        fun b : Borel n => Complex.reCLM (ρ (k⁻¹.val * b.val.val)) from by
          funext b
          rw [hρ, Complex.reCLM_apply, Complex.ofReal_re]]
      exact Complex.reCLM.continuous.comp (ρ.continuous.comp (continuous_const.mul hval))
    have hI := integrable_complexBorelMatrixAverage n μ (fun _ => 1) continuous_const ρ
      (hx := Units.isUnit k⁻¹)
    have hIR : Integrable (fun b : Borel n => w (k⁻¹.val * b.val.val)) μ := by
      simpa only [one_mul, hρ, Complex.reCLM_apply, Complex.ofReal_re, Function.comp_def] using
        Complex.reCLM.integrable_comp hI
    have hPos := integral_pos_of_integrable_nonneg_nonzero (x := (1 : Borel n)) hcts hIR
      (fun b => hw0 (k⁻¹.val * b.val.val))
      (by
        change w (k⁻¹.val * 1) ≠ 0
        rw [mul_one]
        exact (hwPos k⁻¹ ((unitaryCompact ℂ n).inv_mem hk)).ne')
    rw [hJ_int]
    simp_rw [hρ]
    rw [integral_complex_ofReal]
    exact_mod_cast hPos.ne'
  have hJ_ne (g : GL n) : J g ≠ 0 := by
    obtain ⟨b, k, hk, hbk⟩ := exists_borel_mul_unitary n g
    rw [hbk, hJ_cov]
    exact hJ_unitary k hk
  have hInv : ContMDiff (matrixModel ℂ n) (matrixModel ℂ n) ∞ (fun g : GL n => g⁻¹) :=
    contMDiff_inv (matrixModel ℂ n) ∞
  have hVal : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, Mat n) ∞ (Units.val : (GL n) → Mat n) :=
    Units.contMDiff_val
  have hJ : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ J := by
    have hDiff := contDiffOn_complexBorelMatrixAverage n μ (fun _ => 1) continuous_const ρ
    exact (contMDiffOn_iff_contDiffOn.mpr hDiff).comp_contMDiff (hVal.comp hInv)
      (fun g => Units.isUnit g⁻¹)
  let φ (x : GL n) := ρ x.val * (F x⁻¹ / J x⁻¹)
  have hφ : ContMDiff (matrixModel ℂ n) 𝓘(ℝ, ℂ) ∞ φ := by
    let q (z : ℂ × ℂ × ℂ) := z.1 * (z.2.1 / z.2.2)
    have h₁ : ContDiff ℝ ∞ (fun z : ℂ × ℂ × ℂ => z.1) := contDiff_fst
    let S : Set (ℂ × ℂ × ℂ) := {z | z.2.2 ≠ 0}
    have h₂ : ContDiffOn ℝ ∞ (fun z : ℂ × ℂ × ℂ => z.2.1) S := contDiff_snd.fst.contDiffOn
    have h₃ : ContDiffOn ℝ ∞ (fun z : ℂ × ℂ × ℂ => z.2.2) S := contDiff_snd.snd.contDiffOn
    have hInv₃ := h₃.inv (fun _ hz => hz)
    have hq : ContDiffOn ℝ ∞ q S := by
      simpa only [q, div_eq_mul_inv, Pi.mul_apply, Pi.inv_apply] using
        h₁.contDiffOn.mul (h₂.mul hInv₃)
    have hProd := (ρ.contDiff.contMDiff.comp hVal).prodMk_space
      ((hF.comp hInv).prodMk_space (hJ.comp hInv))
    exact (contMDiffOn_iff_contDiffOn.mpr hq).comp_contMDiff hProd (fun x => hJ_ne x⁻¹)
  have hρc := (matrixTestFunctionKernelEquiv ρ).property.2
  have hφc : HasCompactSupport φ := by
    apply hρc.of_isClosed_subset isClosed_closure
    apply closure_mono
    intro x hx h
    apply hx
    change ρ x.val = 0 at h
    change ρ x.val * (F x⁻¹ / J x⁻¹) = 0
    rw [h, zero_mul]
  let f := (matrixTestFunctionKernelEquiv (F := ℂ) (n := n)).symm ⟨φ, hφ, hφc⟩
  have hf (x : GL n) : f x.val = φ x := unitsExtension_val φ x
  refine ⟨f, fun g => ?_⟩
  calc
    complexBorelMatrixAverage n μ η f g⁻¹.val =
        ∫ b : Borel n, (F g / J g) * ρ (g⁻¹.val * b.val.val) ∂μ := by
      unfold complexBorelMatrixAverage
      apply integral_congr_ae (Eventually.of_forall fun b => ?_)
      change η b * f (g⁻¹ * b.val).val = _
      rw [hf]
      have hInvProd : (g⁻¹ * b.val)⁻¹ = (b⁻¹).val * g := by
        rw [mul_inv_rev, inv_inv, Subgroup.coe_inv]
      have hη : η b * η b⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
      dsimp only [φ]
      rw [hInvProd, hCov, hJ_cov]
      calc
        _ = (η b * η b⁻¹) * ((F g / J g) * ρ (g⁻¹.val * b.val.val)) := by
          change η b * (ρ (g⁻¹.val * b.val.val) * (η b⁻¹ * F g / J g)) = _
          simp only [div_eq_mul_inv]
          ring
        _ = _ := by rw [hη, one_mul]
    _ = (F g / J g) * J g := by rw [integral_const_mul, hJ_int]
    _ = F g := div_mul_cancel₀ _ (hJ_ne g)

end Langlands.Archimedean
