import Langlands.Representation.GodementJacquet.Zeta
import Langlands.Representation.RankinSelberg.UnipotentDiagonalVolume
import Langlands.Representation.Hecke.TestFunction
import Langlands.Representation.Whittaker.JPSDilationAssemblyProof

/-!
# The unipotent slice bound for matrix test functions

For a full-matrix test function `Φ` and `k ∈ GL_(n+1)`, the integral of
`|Φ(u diag(a) k)|` over the upper unipotent group is at most a constant times a
monomial `∏ |a_i|^(-e_i)` times the characteristic function of a box. The module
also shows that the matrix integrand of a continuous function is measurable.
See the paired Markdown.
-/

noncomputable section

namespace Langlands.GodementJacquet.WhittakerTorus

open MeasureTheory HarmonicAnalysis RankinSelberg Whittaker GeneralLinear
open scoped BigOperators ENNReal

universe uF

namespace Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance sliceBoundTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance sliceBoundValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance sliceBoundLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance sliceBoundMeasurableSpace (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  borel _
local instance sliceBoundBorelSpace (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance sliceBoundUnipotentMeasurableSpace (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance sliceBoundUnipotentBorelSpace (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

variable {n : ℕ}

/-! ### The box test function -/

/-- The box `{x | ∀ i, |x_i| ≤ ρ}` in `F^(n+1)`. -/
def normBox (n : ℕ) (ρ : ℝ) : Set (Fin (n + 1) → F.Carrier) :=
  Set.univ.pi fun _ => {y : F.Carrier | F.canonicalTopologicalData.normalizedAbs y ≤ ρ}

theorem isClopen_normBox {ρ : ℝ} (hρ : 0 < ρ) : IsClopen (normBox F n ρ) :=
  ⟨isClosed_set_pi fun _ _ =>
      (JPSDilationAssembly.isClopen_le F.canonicalTopologicalData hρ).isClosed,
    isOpen_set_pi Set.finite_univ fun _ _ =>
      (JPSDilationAssembly.isClopen_le F.canonicalTopologicalData hρ).isOpen⟩

theorem isCompact_normBox (ρ : ℝ) : IsCompact (normBox F n ρ) :=
  isCompact_univ_pi fun _ => JPSDilationAssembly.isCompact_le F.canonicalTopologicalData ρ

/-- The characteristic function of `normBox`, as a Schwartz–Bruhat function. -/
def boxTest (n : ℕ) {ρ : ℝ} (hρ : 0 < ρ) : SchwartzBruhat (Fin (n + 1) → F.Carrier) :=
  Hecke.TestFunction.characteristic (isClopen_normBox F hρ) (isCompact_normBox F ρ)

theorem boxTest_apply_of_le {ρ : ℝ} (hρ : 0 < ρ) {x : Fin (n + 1) → F.Carrier}
    (hx : ∀ i, F.canonicalTopologicalData.normalizedAbs (x i) ≤ ρ) :
    boxTest F n hρ x = 1 := by
  simp only [boxTest, Hecke.TestFunction.characteristic_apply]
  exact Set.indicator_of_mem (s := normBox F n ρ) (fun i _ => hx i) _

/-! ### The torus monomial `∏ |a_i|^(-e_i)` -/

/-- The monomial `∏ |a_i|^(-e_i)` of the unipotent volume bound. -/
def torusMonomial (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → F.Carrierˣ) : ℝ :=
  ∏ i, (F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier))⁻¹ ^ e i

theorem torusMonomial_nonneg (e : Fin (n + 1) → ℕ) (a : Fin (n + 1) → F.Carrierˣ) :
    0 ≤ torusMonomial F e a :=
  Finset.prod_nonneg fun _ _ =>
    pow_nonneg (inv_nonneg.2 (F.canonicalTopologicalData.normalizedAbs_nonneg _)) _

/-! ### Measurability and the slice bound -/

theorem measurable_matrixIntegrand {W : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ}
    (hW : Continuous W) (Φ : MatrixTestFunction n F.Carrier) (s : ℂ) :
    Measurable (GodementJacquet.Padic.matrixIntegrand F Φ s W) := by
  have hdet : Continuous fun g : Langlands.GeneralLinear (n + 1) F.Carrier =>
      ((normalizedAbsoluteValue F.canonicalTopologicalData (Matrix.det g.val) : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp (F.canonicalTopologicalData.continuous_normalizedAbs.comp
      Units.continuous_val.matrix_det)
  unfold GodementJacquet.Padic.matrixIntegrand GodementJacquet.matrixIntegrand determinantWeight
  exact ((Φ.continuous.comp Units.continuous_val).measurable.mul hW.measurable).mul
    (hdet.measurable.pow_const s)

/-- **Slice bound.** For a test function `Φ` and `k ∈ GL_(n+1)`, the unipotent
integral of `|Φ(u diag(a) k)|` is at most a constant times
`∏ |a_i|^(-e_i)` times the characteristic function of a box. -/
theorem exists_slice_bound (Φ : MatrixTestFunction n F.Carrier)
    (k : Langlands.GeneralLinear (n + 1) F.Carrier) :
    ∃ (B : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (e : Fin (n + 1) → ℕ), ∀ a : Fin (n + 1) → F.Carrierˣ,
      ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ
          ∂unipotentHaar F.Carrier n ≤
        ENNReal.ofReal B * ENNReal.ofReal (torusMonomial F e a) *
          ‖boxTest F n hρ (fun i => (a i : F.Carrier))‖ₑ := by
  obtain ⟨B, hB⟩ := Φ.continuous.bounded_above_of_compact_support Φ.hasCompactSupport
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0)
  let L : Set (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier) :=
    (fun M => M * (k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val) ''
      tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ)
  have hL : IsCompact L :=
    Φ.hasCompactSupport.isCompact.image (continuous_id.matrix_mul continuous_const)
  obtain ⟨r, C, e, hvol⟩ := unipotentHaar_mul_diagonal_le n L hL
  have hρ : 0 < F.canonicalTopologicalData.normalizedAbs (r : F.Carrier) :=
    F.canonicalTopologicalData.normalizedAbs_pos r.ne_zero
  refine ⟨B * |C|, _, hρ, e, fun a => ?_⟩
  let E : Set (upperUnipotent (n + 1) F.Carrier) :=
    {u | u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) ∈ L}
  have hpt : ∀ u : upperUnipotent (n + 1) F.Carrier,
      ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ ≤
        E.indicator (fun _ => ENNReal.ofReal B) u := by
    intro u
    by_cases hu : u ∈ E
    · rw [Set.indicator_of_mem hu, ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hB _)
    · have hnot : u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val ∉
          tsupport (Φ : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier → ℂ) := by
        intro h
        refine hu ⟨_, h, ?_⟩
        change u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val *
            (k⁻¹ : Langlands.GeneralLinear (n + 1) F.Carrier).val =
          u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier))
        rw [mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
      rw [image_eq_zero_of_notMem_tsupport hnot, enorm_zero]
      exact zero_le
  have hM : 0 ≤ torusMonomial F e a := torusMonomial_nonneg F e a
  calc ∫⁻ u, ‖Φ (u.val.val * Matrix.diagonal (fun i => (a i : F.Carrier)) * k.val)‖ₑ
        ∂unipotentHaar F.Carrier n
      ≤ ∫⁻ u, E.indicator (fun _ => ENNReal.ofReal B) u ∂unipotentHaar F.Carrier n :=
        lintegral_mono hpt
    _ ≤ ENNReal.ofReal B * unipotentHaar F.Carrier n E := lintegral_indicator_const_le E _
    _ ≤ ENNReal.ofReal (B * |C|) * ENNReal.ofReal (torusMonomial F e a) *
          ‖boxTest F n hρ (fun i => (a i : F.Carrier))‖ₑ := by
      by_cases hbox : ∀ i, F.canonicalTopologicalData.normalizedAbs (a i : F.Carrier) ≤
          F.canonicalTopologicalData.normalizedAbs (r : F.Carrier)
      · rw [boxTest_apply_of_le F hρ hbox, enorm_one, mul_one,
          ENNReal.ofReal_mul hB0, mul_assoc]
        gcongr
        refine (hvol a).2.trans ?_
        rw [← ENNReal.ofReal_mul (abs_nonneg C)]
        exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_abs_self C) hM)
      · have hE : E = ∅ :=
          Set.eq_empty_iff_forall_notMem.2 fun u hu => hbox ((hvol a).1 ⟨u, hu⟩)
        rw [hE, measure_empty, mul_zero]
        exact zero_le

end Padic

end Langlands.GodementJacquet.WhittakerTorus
