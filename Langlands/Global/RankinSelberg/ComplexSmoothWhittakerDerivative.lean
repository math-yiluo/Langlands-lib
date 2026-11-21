import Langlands.Global.RankinSelberg.ComplexSmoothWhittakerEquivariance
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.HarmonicAnalysis.Distribution.SmoothTestParameters

/-! # Infinitesimal equivariance for finite-order smooth complex Whittaker functionals -/

noncomputable section

open Set Filter TopologicalSpace
open scoped Classical ContDiff Distributions Matrix.Norms.Operator Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerDerivative

open Langlands.GeneralLinear.UpperBruhatCoordinates (continuous_generalLinear_of_val)
open Langlands.Archimedean (complexPositionCharacter continuous_unitary_toUnits matrixModel
  rightDerivative rightDerivative_mem_principalSeries rightDerivative_eq_fderiv unitsExtension
  differentiableAt_unitsExtension unitsExtension_val)
open Langlands.Archimedean.UnitaryFinitePolynomial (compactSpace_unitary)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter complexScaledCharacter_apply)
open Langlands.HarmonicAnalysis (compactTestFamily continuous_compactTestFamily smoothTimeDifferenceQuotient
  contDiff_smoothTimeDifferenceQuotient smoothTimeDifferenceQuotient_zero smul_smoothTimeDifferenceQuotient)
open ComplexWhittakerSmoothExtension (SmoothStandard compactProfile exists_smooth_matrix_extension)
open ComplexWhittakerTranslateExtension (smoothTranslate)
open ComplexCompactSmoothDifferences (CompactProfileDifferenceBound complexCompactSmoothDifferences)

local notation "Mat" => fun n => Matrix (Fin n) (Fin n) ℂ
local notation "G" => fun n => Langlands.GeneralLinear n ℂ
local notation "K" => fun n => Matrix.unitaryGroup (Fin n) ℂ

variable {n : ℕ} {ds : List ComplexCharacterData}

/-- The right derivative acts on the original smooth standard module. -/
def smoothDerivative (X : Mat n) (F : SmoothStandard n ds) : SmoothStandard n ds :=
  ⟨rightDerivative (matrixModel ℂ n) X F.val,
    rightDerivative_mem_principalSeries (complexPositionCharacter ds) F.2 X⟩

@[simp] theorem smoothDerivative_apply (X : Mat n) (F : SmoothStandard n ds) (g : G n) :
    (smoothDerivative X F).val g = rightDerivative (matrixModel ℂ n) X F.val g := rfl

private theorem timeQuotient_zero_off {S : Compacts (Mat n)} {h : ℝ × Mat n → ℂ}
    (hh : ContDiff ℝ ∞ h) (hz : ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ X ∉ S, h (t, X) = 0) :
    ∀ t ∈ Ioo (-1 : ℝ) 1, ∀ X ∉ S, smoothTimeDifferenceQuotient h (t, X) = 0 := by
  have h0 : (0 : ℝ) ∈ Ioo (-1 : ℝ) 1 := by norm_num
  intro t ht X hX
  by_cases ht0 : t = 0
  · subst t
    have he : (fun u : ℝ => h (u, X)) =ᶠ[𝓝 0] (fun _ => (0 : ℂ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with u hu
      exact hz u hu X hX
    have hp : HasDerivAt (fun u : ℝ => (u, X)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 X)
    have hd := ((hh.differentiable (by simp) (0, X)).hasFDerivAt.comp_hasDerivAt 0 hp).deriv
    rw [smoothTimeDifferenceQuotient_zero, ← hd]
    change deriv (fun u : ℝ => h (u, X)) 0 = 0
    rw [he.deriv_eq, deriv_const]
  · have he := smul_smoothTimeDifferenceQuotient hh t X
    rw [hz t ht X hX, hz 0 h0 X hX, sub_self] at he
    exact (smul_eq_zero.mp he).resolve_left ht0

set_option maxHeartbeats 900000 in
private theorem eval_smoothDerivative_of_path (L : SmoothStandard n ds →ₗ[ℂ] ℂ)
    (J : ℕ) (C : ℝ) (hL : ∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R)
    (X : Mat n) (u : ℝ → G n) (hu : ∀ t, (u t).val = 1 + t • X)
    (c : ℝ → ℂ) (hc : ContDiff ℝ ∞ c) (hc0 : c 0 = 1) (freq : ℂ) (hc' : HasDerivAt c freq 0)
    (hCov : ∀ t F, L (smoothTranslate (u t) F) = c t * L F) (F : SmoothStandard n ds) :
    L (smoothDerivative X F) = freq * L F := by
  let : CompactSpace (K n) := compactSpace_unitary n
  let s := Ioo (-1 : ℝ) 1
  have h0 : (0 : ℝ) ∈ s := by norm_num [s]
  let o : s := ⟨0, h0⟩
  have hu0 : u 0 = 1 := by apply Units.ext; rw [hu, zero_smul, add_zero, Units.val_one]
  have huc : Continuous u := continuous_generalLinear_of_val (by
    simp_rw [hu]
    exact continuous_const.add (continuous_id.smul continuous_const))
  let kMove (q : ℝ × K n) := Unitary.toUnits q.2 * u q.1
  let S := (fun q => (kMove q).val) '' (Icc (-1 : ℝ) 1 ×ˢ (univ : Set (K n)))
  have hS : IsCompact S := (isCompact_Icc.prod isCompact_univ).image
    (Units.continuous_val.comp ((continuous_unitary_toUnits.comp continuous_snd).mul (huc.comp continuous_fst)))
  obtain ⟨H, hH, hHc, hA⟩ := exists_smooth_matrix_extension hS
    (fun _ ⟨q, _, hq⟩ => hq ▸ (kMove q).isUnit) F.2.1
  have hAgree (t : ℝ) (ht : t ∈ Icc (-1 : ℝ) 1) (k : K n) :
      H (k.val * (1 + t • X)) = F.val (Unitary.toUnits k * u t) := by
    have he : (kMove (t, k)).val = k.val * (1 + t • X) := by
      change k.val * (u t).val = _
      rw [hu]
    rw [← he]
    exact hA (kMove (t, k)) ⟨(t, k), ⟨ht, mem_univ k⟩, rfl⟩
  have hH0 (k : K n) : H k.val = F.val (Unitary.toUnits k) := by
    simpa only [zero_smul, add_zero, mul_one, hu0] using hAgree 0 (by norm_num) k
  let h (q : ℝ × Mat n) := H (q.2 * (1 + q.1 • X)) - c q.1 * H q.2
  have hh : ContDiff ℝ ∞ h := (hH.comp
    (contDiff_snd.mul (contDiff_const.add (contDiff_fst.smul contDiff_const)))).sub
      ((hc.comp contDiff_fst).mul (hH.comp contDiff_snd))
  let moveBack (q : ℝ × Mat n) : Mat n := q.2 * (u q.1)⁻¹.val
  have hmc : Continuous moveBack := continuous_snd.mul (Units.continuous_val.comp (huc.inv.comp continuous_fst))
  let T : Compacts (Mat n) := ⟨tsupport H ∪ moveBack '' (Icc (-1 : ℝ) 1 ×ˢ tsupport H),
    hHc.union ((isCompact_Icc.prod hHc).image hmc)⟩
  have hz : ∀ t ∈ s, ∀ Y ∉ T, h (t, Y) = 0 := by
    intro t ht Y hY
    have hY0 : H Y = 0 := image_eq_zero_of_notMem_tsupport (fun hy => hY (Or.inl hy))
    have hyU : Y * (1 + t • X) ∉ tsupport H := by
      intro hy
      apply hY
      right
      refine ⟨(t, Y * (1 + t • X)), ⟨Ioo_subset_Icc_self ht, hy⟩, ?_⟩
      dsimp only [moveBack]
      rw [← hu, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
    change H (Y * (1 + t • X)) - c t * H Y = 0
    rw [hY0, image_eq_zero_of_notMem_tsupport hyU, mul_zero, sub_self]
  let Q (t : s) : 𝓓_{T}(Mat n, ℂ) := compactTestFamily (contDiff_smoothTimeDifferenceQuotient hh)
    (timeQuotient_zero_off hh hz) t
  have hQc : Continuous Q := continuous_compactTestFamily _ _
  let P := smoothDerivative X F - freq • F
  have hQ0 (k : K n) : Q o k.val = compactProfile P k := by
    change smoothTimeDifferenceQuotient h (0, k.val) = _
    rw [smoothTimeDifferenceQuotient_zero]
    have hp : HasDerivAt (fun t : ℝ => (t, k.val)) (1, 0) 0 :=
      (hasDerivAt_id 0).prodMk (hasDerivAt_const 0 k.val)
    have hd := ((hh.differentiable (by simp) (0, k.val)).hasFDerivAt.comp_hasDerivAt 0 hp).deriv
    rw [← hd]
    let g : G n := Unitary.toUnits k
    let y (t : ℝ) : Mat n := g.val + t • (g.val * X)
    have hy (t : ℝ) : (g * u t).val = y t := by
      rw [Units.val_mul, hu, mul_add, mul_one, Matrix.mul_smul]
    have hEq : (fun t : ℝ => h (t, k.val)) =ᶠ[𝓝 0]
        (fun t : ℝ => unitsExtension F.val (y t) - c t * F.val g) := by
      filter_upwards [isOpen_Ioo.mem_nhds h0] with t ht
      change H (k.val * (1 + t • X)) - c t * H k.val = _
      rw [hAgree t (Ioo_subset_Icc_self ht) k, hH0 k, ← hy, unitsExtension_val]
    change deriv (fun t : ℝ => h (t, k.val)) 0 = _
    rw [hEq.deriv_eq]
    have hyd : HasDerivAt y (g.val * X) 0 := by
      simpa only [y, id_eq, one_smul] using ((hasDerivAt_id (0 : ℝ)).smul_const (g.val * X)).const_add g.val
    have hF := (differentiableAt_unitsExtension F.2.1 g.isUnit).hasFDerivAt
    have hY := hF.comp_hasDerivAt_of_eq 0 hyd (by simp [y])
    have hDeriv : HasDerivAt (fun t : ℝ => unitsExtension F.val (y t) - c t * F.val g)
        (fderiv ℝ (unitsExtension F.val) g.val (g.val * X) - freq * F.val g) 0 :=
      hY.sub (hc'.mul_const (F.val g))
    rw [hDeriv.deriv]
    change fderiv ℝ (unitsExtension F.val) g.val (g.val * X) - freq * F.val g =
      rightDerivative (matrixModel ℂ n) X F.val g - freq * F.val g
    rw [rightDerivative_eq_fderiv F.2.1]
  let V (t : s) : SmoothStandard n ds := (t.val⁻¹ : ℝ) • (smoothTranslate (u t.val) F - c t.val • F)
  have hV0 (t : s) : L (V t) = 0 := by
    dsimp only [V]
    rw [LinearMap.map_smul_of_tower, map_sub, hCov, map_smul, smul_eq_mul, sub_self, smul_zero]
  have hQV (t : s) (ht : t.val ≠ 0) (k : K n) : Q t k.val = compactProfile (V t) k := by
    have hd := smul_smoothTimeDifferenceQuotient hh t.val k.val
    have hE : h (t.val, k.val) = F.val (Unitary.toUnits k * u t.val) - c t.val * F.val (Unitary.toUnits k) := by
      dsimp only [h]
      rw [hAgree t.val (Ioo_subset_Icc_self t.2), hH0]
    have hE0 : h (0, k.val) = 0 := by simp [h, hc0]
    change smoothTimeDifferenceQuotient h (t.val, k.val) =
      t.val⁻¹ • (F.val (Unitary.toUnits k * u t.val) - c t.val * F.val (Unitary.toUnits k))
    rw [← inv_smul_smul₀ ht (smoothTimeDifferenceQuotient h (t.val, k.val)), hd, hE, hE0, sub_zero]
  obtain ⟨D, hD, hDiff⟩ := complexCompactSmoothDifferences n J
  let sem := ContDiffMapSupportedIn.supSeminorm ℝ (Mat n) ℂ ⊤ T J
  let bound (t : s) := C * (D * sem (Q o - Q t))
  have hCont : Continuous bound := continuous_const.mul (continuous_const.mul
    (((ContDiffMapSupportedIn.withSeminorms' ℝ (Mat n) ℂ ⊤ T).continuous_seminorm J).comp
      (continuous_const.sub hQc)))
  have hLe (t : s) (ht : t.val ≠ 0) : ‖L P‖ ≤ bound t := by
    have hProfile : compactProfile (P - V t) = fun k : K n => (Q o - Q t) k.val := by
      funext k
      change compactProfile P k - compactProfile (V t) k = Q o k.val - Q t k.val
      rw [hQ0, hQV t ht]
    let f := Q o - Q t
    have hb : CompactProfileDifferenceBound J (compactProfile (P - V t)) (D * sem f) := by
      rw [hProfile]
      refine hDiff f (sem f) f.contDiff (apply_nonneg _ _) (fun i hi Y _ => ?_)
      exact (ContDiffMapSupportedIn.norm_iteratedFDeriv_apply_le_seminorm_top ℝ).trans
        (Seminorm.le_finset_sup_apply (Finset.mem_Iic.mpr hi))
    have hB := hL _ _ hb
    rw [map_sub, hV0, sub_zero] at hB
    exact hB
  have hClosed : IsClosed {t : s | ‖L P‖ ≤ bound t} := isClosed_le continuous_const hCont
  have hDense : Dense ((Subtype.val : s → ℝ) ⁻¹' ({0} : Set ℝ)ᶜ) :=
    (dense_compl_singleton 0).preimage isOpen_Ioo.isOpenMap_subtype_val
  have ho : ‖L P‖ ≤ bound o := (closure_minimal
    (fun t ht => hLe t (mem_compl_singleton_iff.mp ht)) hClosed) (hDense o)
  have hLP : L P = 0 := norm_eq_zero.mp (le_antisymm (by simpa [bound, sem] using ho) (norm_nonneg _))
  change L (smoothDerivative X F - freq • F) = 0 at hLP
  rw [map_sub, map_smul, smul_eq_mul] at hLP
  exact sub_eq_zero.mp hLP

section Unipotent

variable {r : ℕ}

private def upperLine (X : Mat (r + 1)) (hX : ∀ i j, j ≤ i → X i j = 0) (t : ℝ) :
    Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ := by
  have ht : (1 + t • X).IsUpperTriangular := fun i j hij => by
    change j < i at hij
    simp [Matrix.add_apply, Matrix.smul_apply, hX i j hij.le, Matrix.one_apply_ne hij.ne']
  have hd (i : Fin (r + 1)) : (1 + t • X) i i = 1 := by
    simp [Matrix.add_apply, Matrix.smul_apply, hX i i le_rfl]
  have hdet : Matrix.det (1 + t • X) = 1 := by rw [Matrix.det_of_isUpperTriangular ht]; simp [hd]
  exact ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ (hdet ▸ one_ne_zero), ht, hd⟩

set_option maxHeartbeats 700000 in
private theorem character_upperLine (a : ℂˣ) (X : Mat (r + 1))
    (hX : ∀ i j, j ≤ i → X i j = 0) (t : ℝ) :
    complexWhittakerCharacter a (upperLine X hX t).val =
      Complex.exp ((t : ℂ) * complexWhittakerFrequency a X) := by
  change (complexScaledCharacter a).complex (∑ i : Fin r, (1 + t • X) i.castSucc i.succ) = _
  simp only [Langlands.HarmonicAnalysis.UnitaryAdditiveCharacter.complex_apply,
    complexScaledCharacter_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.one_apply_ne (ne_of_lt Fin.castSucc_lt_succ), zero_add]
  rw [← Finset.smul_sum, mul_smul_comm, map_smul, smul_eq_mul, Real.fourierChar_apply]
  congr 1
  unfold complexWhittakerFrequency
  push_cast
  ring

/-- Finite compact difference order lets the group Whittaker character law be
differentiated on the original smooth complex standard module. -/
def ComplexSmoothWhittakerDerivativeStatement : Prop :=
  ∀ (r : ℕ) (ds : List ComplexCharacterData) (a : ℂˣ)
    (L : SmoothStandard (r + 1) ds →ₗ[ℂ] ℂ) (J : ℕ) (C : ℝ),
    (∀ F R, CompactProfileDifferenceBound J (compactProfile F) R → ‖L F‖ ≤ C * R) →
    (∀ F (u : G (r + 1)), u ∈ Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ →
      L (smoothTranslate u F) = complexWhittakerCharacter a u * L F) →
    ∀ (F : SmoothStandard (r + 1) ds) (X : Mat (r + 1)), (∀ i j, j ≤ i → X i j = 0) →
      L (smoothDerivative X F) = complexWhittakerFrequency a X * L F

set_option maxHeartbeats 900000 in
theorem complexSmoothWhittakerDerivative : ComplexSmoothWhittakerDerivativeStatement := by
  intro r ds a L J C hL hCov F X hX
  let freq := complexWhittakerFrequency a X
  let c (t : ℝ) := Complex.exp ((t : ℂ) * freq)
  have hc : ContDiff ℝ ∞ c :=
    ((Complex.ofRealCLM.contDiff : ContDiff ℝ ∞ fun t : ℝ => (t : ℂ)).mul contDiff_const).cexp
  have hc' : HasDerivAt c freq 0 := by
    simpa [c] using (((hasDerivAt_id (0 : ℝ)).ofReal_comp).mul_const freq).cexp
  exact eval_smoothDerivative_of_path L J C hL X (fun t => (upperLine X hX t).val) (fun _ => rfl)
    c hc (by simp [c]) freq hc' (fun t F' => by
      rw [hCov F' _ (upperLine X hX t).2, character_upperLine]) F

end Unipotent
end Langlands.Global.RankinSelbergGlobal.ComplexSmoothWhittakerDerivative
