import Langlands.Global.RankinSelberg.ComplexGodementNonzeroTest
import Langlands.Global.RankinSelberg.ComplexGodementUnitaryAverage

/-! # Detection by a compact-finite full-row-rank Godement test -/

noncomputable section
open MeasureTheory Set Filter
open scoped Classical ContDiff Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean (continuous_unitary_toUnits unitaryCompact)
open Langlands.Archimedean.UnitaryFinitePolynomial (polynomialStar polynomialStar_separatesPoints)
open Langlands.GeneralLinear (determinant determinantContinuous)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rowMeasure rectangularJoin rectangularLastColumn
  continuous_rectangularJoin continuous_rectangularLastColumn rectangularLastColumn_join)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz EntrySchwartz operatorToEntry operatorToEntry_apply)
open ComplexGodementAddedCharacter (continuedValue rightTest rightTest_apply)
open ComplexGodementColumnChange (columnIntegral iteratedKernel)
open ComplexGodementContinuedSmooth (translatedIntegral contMDiff_translatedIntegral)
open ComplexGodementTranslatedBounds (complexGodementTranslatedBounds rightTestSize
  continuous_rightTestSize one_le_rightTestSize)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel
local instance finiteNonzeroUnitaryMeasure (m : ℕ) : MeasurableSpace (Matrix.unitaryGroup (Fin m) ℂ) := borel _
local instance finiteNonzeroUnitaryBorel (m : ℕ) : BorelSpace (Matrix.unitaryGroup (Fin m) ℂ) := ⟨rfl⟩

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G'" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "K" => Matrix.unitaryGroup (Fin (r + 1 + 1)) ℂ
local notation "Rect" => Matrix (Fin (r + 1)) (Fin (r + 1 + 1)) ℂ
local notation "Col" => Fin (r + 1) → ℂ
local notation "Test" => OperatorSchwartz (r + 1) (r + 1 + 1)
local notation "EntryTest" => EntrySchwartz (r + 1) (r + 1 + 1)
local notation "κ" => compactMatrixHaar (r + 1 + 1)

private def columnPoint (h : G) (y : Col) : Rect := rectangularJoin h.val (h.val.mulVec y)

private theorem continuous_columnPoint : Continuous (fun p : G × Col => columnPoint p.1 p.2) := by
  have hc : Continuous (fun p : G × Col => p.1.val) := Units.continuous_val.comp continuous_fst
  exact continuous_rectangularJoin.comp (hc.prodMk (hc.matrix_mulVec continuous_snd))

private def unitaryColumn (a : ℂˣ) (Φ : Test) (h : G) (k : K) (y : Col) : ℂ :=
  Φ (columnPoint h y * k.val) * (complexScaledCharacter a).complex (y (Fin.last r))

private theorem continuous_unitaryColumn (a : ℂˣ) (Φ : Test) :
    Continuous (fun p : (G × K) × Col => unitaryColumn a Φ p.1.1 p.1.2 p.2) :=
  ((operatorToEntry Φ).continuous.comp
    ((continuous_columnPoint.comp (continuous_fst.fst.prodMk continuous_snd)).matrix_mul
      (continuous_subtype_val.comp continuous_fst.snd))).mul
    ((complexScaledCharacter a).continuous_complex.comp ((continuous_apply (Fin.last r)).comp continuous_snd))

private def rightMatrix (k : K) (X : Rect) : Rect := X * k.val

private theorem rightMatrix_inverse (k : K) (X : Rect) : rightMatrix k⁻¹ (rightMatrix k X) = X := by
  change (X * (Unitary.toUnits k).val) * (Unitary.toUnits k)⁻¹.val = X
  rw [Matrix.mul_assoc, Units.mul_inv, Matrix.mul_one]

private theorem columnPoint_restore (h : G) (y : Col) (k : K) :
    h⁻¹.val.mulVec (rectangularLastColumn (rightMatrix k⁻¹ (rightMatrix k (columnPoint h y)))) = y := by
  rw [rightMatrix_inverse, columnPoint, rectangularLastColumn_join,
    Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]

set_option maxHeartbeats 800000 in
private theorem columnAverage_integrable (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (w : C(K, ℂ)) (Φ : Test) (hΦ : HasCompactSupport Φ) (h : G) :
    Integrable (fun p : Col × K => w p.2 * unitaryColumn a Φ h p.2 p.1) ((rowMeasure μ (r + 1)).prod κ) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let B (p : Rect × K) := (h⁻¹.val.mulVec (rectangularLastColumn (rightMatrix p.2⁻¹ p.1)), p.2)
  have hB : Continuous B := (continuous_const.matrix_mulVec (continuous_rectangularLastColumn.comp
    (continuous_fst.matrix_mul (continuous_subtype_val.comp continuous_snd.inv)))).prodMk continuous_snd
  have ht : Continuous (fun p : Col × K => ((h, p.2), p.1)) :=
    (continuous_const.prodMk continuous_snd).prodMk continuous_fst
  have hu : Continuous (fun p : Col × K => unitaryColumn a Φ h p.2 p.1) := by
    change Continuous ((fun p : (G × K) × Col => unitaryColumn a Φ p.1.1 p.1.2 p.2) ∘
      (fun p : Col × K => ((h, p.2), p.1)))
    exact (continuous_unitaryColumn (r := r) a Φ).comp ht
  have hc : Continuous (fun p : Col × K => w p.2 * unitaryColumn a Φ h p.2 p.1) :=
    (w.continuous.comp continuous_snd).mul hu
  apply hc.integrable_of_hasCompactSupport
  apply HasCompactSupport.of_support_subset_isCompact ((hΦ.prod isCompact_univ).image hB)
  intro ⟨y, k⟩ hy
  let X := rightMatrix k (columnPoint h y)
  have hX : X ∈ tsupport Φ := by
    apply subset_tsupport
    intro hz
    apply hy
    change w k * (Φ X * _) = 0
    rw [hz, zero_mul, mul_zero]
  exact ⟨(X, k), ⟨hX, mem_univ _⟩, Prod.ext (columnPoint_restore h y k) rfl⟩

private theorem rightTest_one (Φ : EntryTest) : rightTest (1 : G') Φ = Φ := by
  ext X
  rw [rightTest_apply, Units.val_one, Matrix.mul_one]

private theorem columnIntegral_unitaryAverage (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (w : C(K, ℂ)) (Φ : Test) (hΦ : HasCompactSupport Φ) (h : G) :
    columnIntegral (complexScaledCharacter a) μ (operatorToEntry (unitaryAverage w Φ)) h =
      ∫ k : K, w k * columnIntegral (complexScaledCharacter a) μ
        (rightTest (Unitary.toUnits k) (operatorToEntry Φ)) h ∂κ := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  calc
    _ = ∫ y, ∫ k : K, w k * unitaryColumn a Φ h k y ∂κ ∂rowMeasure μ (r + 1) := by
      unfold columnIntegral
      refine integral_congr_ae (ae_of_all _ fun y => ?_)
      change operatorToEntry (unitaryAverage w Φ) (columnPoint h y) * _ = _
      rw [operatorToEntry_apply, unitaryAverage_apply, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun k => mul_assoc _ _ _)
    _ = ∫ k : K, ∫ y, w k * unitaryColumn a Φ h k y ∂rowMeasure μ (r + 1) ∂κ :=
      integral_integral_swap (columnAverage_integrable μ a w Φ hΦ h)
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      change (∫ y, w k * unitaryColumn a Φ h k y ∂rowMeasure μ (r + 1)) =
        w k * columnIntegral (complexScaledCharacter a) μ (rightTest (Unitary.toUnits k) (operatorToEntry Φ)) h
      rw [columnIntegral, ← integral_const_mul]
      exact integral_congr_ae (ae_of_all _ fun y => by
        simp only [unitaryColumn, columnPoint, rightTest_apply, operatorToEntry_apply]
        rfl)

private theorem continuous_detPower_for_average (s : ℂ) :
    Continuous (fun h : G => ArchimedeanLocal.detPower complexNormalizedAbs h s) :=
  (continuous_const.mul (Complex.continuous_ofReal.comp
    ((Units.continuous_val.matrix_det.norm.pow 2).log fun h : G =>
      pow_ne_zero 2 (norm_ne_zero_iff.mpr h.det_ne_zero)))).cexp

private theorem stronglyMeasurable_weightedIteratedKernel (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (W : G → ℂ) (hW : Continuous W) (s : ℂ) (w : C(K, ℂ)) (Φ : Test) :
    StronglyMeasurable (fun p : G × K => w p.2 * iteratedKernel (complexScaledCharacter a) μ d
      (rightTest (Unitary.toUnits p.2) (operatorToEntry Φ)) W s p.1) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  have hI : StronglyMeasurable (fun p : G × K => ∫ y, unitaryColumn a Φ p.1 p.2 y ∂rowMeasure μ (r + 1)) :=
    (continuous_unitaryColumn a Φ).stronglyMeasurable.integral_prod_right'
  have hD := Units.continuous_val.comp (d.character.continuous.comp
    (determinantContinuous.continuous.comp (continuous_fst : Continuous (Prod.fst : G × K → G))))
  have h := (w.continuous.comp continuous_snd).stronglyMeasurable.mul
    (((hI.mul (hW.comp continuous_fst.inv).stronglyMeasurable).mul hD.stronglyMeasurable).mul
      ((continuous_detPower_for_average s).comp continuous_fst).stronglyMeasurable)
  exact h

set_option maxHeartbeats 1300000 in
/-- The continued outer integral at the identity commutes with a weighted unitary average
of a compact test. -/
theorem translatedIntegral_unitaryAverage {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (s : ℂ) (w : C(K, ℂ)) (Φ : Test) (hΦ : HasCompactSupport Φ) :
    translatedIntegral ν μ a d (W p) s (operatorToEntry (unitaryAverage w Φ)) 1 =
      ∫ k : K, w k * translatedIntegral ν μ a d (W p) s (operatorToEntry Φ) (Unitary.toUnits k) ∂κ := by
  let Φₑ := operatorToEntry Φ
  let F (q : G × K) := w q.2 * iteratedKernel (complexScaledCharacter a) μ d
    (rightTest (Unitary.toUnits q.2) Φₑ) (W p) s q.1
  obtain ⟨I, N, B, hBi, hB₀, hb⟩ := complexGodementTranslatedBounds ν μ a d S W hWc hWb
    |(s - 1).re| (abs_nonneg _)
  let C := I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φₑ
  obtain ⟨M, hM⟩ := (isCompact_univ : IsCompact (univ : Set K)).exists_bound_of_continuousOn
    w.continuous.continuousOn
  obtain ⟨L, hL⟩ := (isCompact_univ : IsCompact (univ : Set K)).exists_bound_of_continuousOn
    (continuous_rightTestSize.comp continuous_unitary_toUnits).continuousOn
  let R := max M 0 * (max L 1 ^ N * C)
  have hFi : Integrable F (ν.prod κ) := by
    refine ((hBi.mul_const R).comp_fst κ).mono'
      (stronglyMeasurable_weightedIteratedKernel μ a d (W p) (hWc p hp) s w Φ).aestronglyMeasurable ?_
    refine ae_of_all _ fun q => ?_
    have hq := hb p hp s le_rfl (Unitary.toUnits q.2) Φₑ
    have hsize := (le_abs_self _).trans (hL q.2 (mem_univ _))
    have hn := (zero_le_one.trans (one_le_rightTestSize (Unitary.toUnits q.2)))
    have hC : 0 ≤ C := apply_nonneg _ _
    change ‖F q‖ ≤ B q.1 * R
    dsimp only [F]
    rw [norm_mul]
    calc
      _ ≤ max M 0 * (B q.1 * rightTestSize (Unitary.toUnits q.2) ^ N * C) :=
        mul_le_mul ((hM q.2 (mem_univ _)).trans (le_max_left _ _)) (hq.2.1 q.1)
          (norm_nonneg _) (le_max_right _ _)
      _ = B q.1 * (max M 0 * (rightTestSize (Unitary.toUnits q.2) ^ N * C)) := by ring
      _ ≤ B q.1 * R := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hn (hsize.trans (le_max_left _ _)) N) hC)
          (le_max_right _ _)) (hB₀ q.1)
  calc
    _ = ∫ h, ∫ k : K, F (h, k) ∂κ ∂ν := by
      unfold translatedIntegral
      rw [rightTest_one]
      refine integral_congr_ae (ae_of_all _ fun h => ?_)
      rw [iteratedKernel, columnIntegral_unitaryAverage μ a w Φ hΦ h,
        ← integral_mul_const, ← integral_mul_const, ← integral_mul_const]
      exact integral_congr_ae (ae_of_all _ fun k => by dsimp [F, iteratedKernel]; ring)
    _ = ∫ k : K, ∫ h, F (h, k) ∂ν ∂κ := integral_integral_swap hFi
    _ = _ := by
      refine integral_congr_ae (ae_of_all _ fun k => ?_)
      change (∫ h, F (h, k) ∂ν) = w k * (∫ h, iteratedKernel (complexScaledCharacter a) μ d
        (rightTest (Unitary.toUnits k) Φₑ) (W p) s h ∂ν)
      rw [← integral_const_mul]

private theorem exists_polynomial_weight (f : C(K, ℂ)) (hf : f 1 ≠ 0) :
    ∃ w ∈ polynomialStar (r + 1 + 1), (∫ k, w k * f k ∂κ) ≠ 0 := by
  by_contra! h
  let L (w : C(K, ℂ)) : ℂ := ∫ k, (w * f) k ∂κ
  have hL : Continuous L := by
    have hmul : Continuous (fun w : C(K, ℂ) => w * f) := continuous_id.mul continuous_const
    have hI : Continuous (fun u : Lp ℂ 1 κ => ∫ k, u k ∂κ) := continuous_integral
    have hLp := (ContinuousMap.toLp (E := ℂ) 1 κ ℂ).continuous
    apply (hI.comp (hLp.comp hmul)).congr
    intro w
    exact integral_congr_ae (ContinuousMap.coeFn_toLp (E := ℂ) (p := 1) (𝕜 := ℂ) κ (w * f))
  have hs : (polynomialStar (r + 1 + 1) : Set C(K, ℂ)) ⊆ {w | L w = 0} := fun w hw => h w hw
  have hd := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints
    (polynomialStar (r + 1 + 1)) polynomialStar_separatesPoints
  have ht : star f ∈ closure (polynomialStar (r + 1 + 1) : Set C(K, ℂ)) := by
    rw [← StarSubalgebra.topologicalClosure_coe, hd]
    exact StarSubalgebra.mem_top
  have hz : L (star f) = 0 := closure_minimal hs (isClosed_eq hL continuous_const) ht
  have hpt (k : K) : (star f * f) k = ((‖f k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [ContinuousMap.mul_apply, ContinuousMap.star_apply]
    rw [Complex.star_def, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hre : ∫ k, ‖f k‖ ^ 2 ∂κ = 0 := by
    simp only [L, hpt, integral_complex_ofReal] at hz
    exact_mod_cast hz
  have hcont : Continuous (fun k : K => ‖f k‖ ^ 2) := f.continuous.norm.pow 2
  have hi : Integrable (fun k : K => ‖f k‖ ^ 2) κ :=
    hcont.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hae := (integral_eq_zero_iff_of_nonneg (fun k : K => sq_nonneg ‖f k‖) hi).mp hre
  have heq := (Continuous.ae_eq_iff_eq κ hcont continuous_const).mp hae
  have h1 := congrFun heq (1 : K)
  change ‖f 1‖ ^ 2 = 0 at h1
  exact hf (norm_eq_zero.mp ((pow_eq_zero_iff (by decide : (2 : ℕ) ≠ 0)).mp h1))

open scoped Matrix.Norms.Operator Manifold in
set_option maxHeartbeats 750000 in
/-- A nonzero smaller-rank value is detected by a compact full-rank Schwartz test with
finite-dimensional right unitary translate span. -/
theorem exists_finite_test_continuedValue_ne_zero {P : Type} (ν : Measure G) [ν.IsHaarMeasure]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ)
    (hWc : ∀ p ∈ S, Continuous (W p)) (hWb : HasUniformSimpleRootBound S W)
    (p : P) (hp : p ∈ S) (hW : W p 1 ≠ 0) (s : ℂ) :
    ∃ Φ : Test, HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (r + 1 + 1) =>
        translateTest k.val Φ)) ∧ continuedValue ν μ d a (operatorToEntry Φ) (W p) 1 s ≠ 0 := by
  obtain ⟨Φ, hΦ, hfull, hne⟩ := exists_compact_test_continuedValue_ne_zero ν μ a d S W hWc hWb p hp hW s
  let t : ℂ := (((r + 1 : ℕ) + 1 : ℂ) / 2) + s
  let c : ℂ := ((d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
    characterWeight d (((r + 1 : ℕ) : ℂ) / 2) (determinant (1 : G'))) *
      ArchimedeanLocal.detPower complexNormalizedAbs (1 : G') s
  have hval (Ψ : Test) : continuedValue ν μ d a (operatorToEntry Ψ) (W p) 1 s =
      c * translatedIntegral ν μ a d (W p) t (operatorToEntry Ψ) 1 := rfl
  rw [hval] at hne
  have hc : c ≠ 0 := left_ne_zero_of_mul hne
  let f : C(K, ℂ) := ⟨fun k => translatedIntegral ν μ a d (W p) t (operatorToEntry Φ) (Unitary.toUnits k),
    (contMDiff_translatedIntegral ν μ a d W hWc hWb hp t (operatorToEntry Φ)).continuous.comp
      continuous_unitary_toUnits⟩
  have hf : f 1 ≠ 0 := by
    change translatedIntegral ν μ a d (W p) t (operatorToEntry Φ) (Unitary.toUnits 1) ≠ 0
    rw [map_one]
    exact right_ne_zero_of_mul hne
  obtain ⟨w, hw, hwne⟩ := exists_polynomial_weight f hf
  obtain ⟨hΨ, hΨfull⟩ := unitaryAverage_support w Φ hΦ hfull
  refine ⟨unitaryAverage w Φ, hΨ, hΨfull, unitaryAverage_finite hw Φ, ?_⟩
  rw [hval, translatedIntegral_unitaryAverage ν μ a d S W hWc hWb p hp t w Φ hΦ]
  exact mul_ne_zero hc hwne

variable (r) in
/-- Compact-finite detection of a nonzero smaller-rank value in the continued Godement formula. -/
def ComplexGodementFiniteNonzeroStatement : Prop :=
  ∀ {P : Type} (ν : Measure G) [ν.IsHaarMeasure] (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (S : Set P) (W : P → G → ℂ),
    (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, W p 1 ≠ 0 → ∀ s : ℂ,
      ∃ Φ : Test, HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
        FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ (r + 1 + 1) =>
          translateTest k.val Φ)) ∧ continuedValue ν μ d a (operatorToEntry Φ) (W p) 1 s ≠ 0

theorem complexGodementFiniteNonzero : ComplexGodementFiniteNonzeroStatement r := by
  intro P ν hν μ a d S W hWc hWb p hp hW s
  exact exists_finite_test_continuedValue_ne_zero ν μ a d S W hWc hWb p hp hW s

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
