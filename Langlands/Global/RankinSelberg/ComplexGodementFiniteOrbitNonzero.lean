import Langlands.Global.RankinSelberg.ComplexGodementLocalizedNonzero
import Langlands.Global.RankinSelberg.ComplexGodementParametric
import Langlands.Global.RankinSelberg.ComplexGodementKFinite
import Langlands.Representation.Archimedean.UnitaryFinitePolynomial

/-! # Finite unitary orbit and nonvanishing for the continued Godement integral -/

noncomputable section

open MeasureTheory Set
open scoped Classical Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter

open Langlands.Archimedean (unitaryCompact continuous_unitary_toUnits)
open Langlands.Archimedean.ComplexMaximalParabolicIntegration (normSqC_ne_zero)
open Langlands.Archimedean.UnitaryFinitePolynomial (polynomialStar polynomialStar_toSubalgebra
  separated inv_mul_mem_separated eq_zero_of_integral_polynomial_mul_eq_zero integrable_of_continuous)
open Langlands.GeneralLinear (determinant)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure rectangularJoin rectangularLastColumn
  continuous_rectangularJoin continuous_rectangularLastColumn rowMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter)
open ComplexGodement (HasFullRowRank characterWeight continuous_characterWeight translateTest)
open ComplexGodementColumnChange (iteratedKernel columnIntegral)
open ComplexGodementWhittakerFamily (HasUniformSimpleRootBound)
open ComplexGodementTranslatedBounds (complexGodementTranslatedBounds rightTestSize
  continuous_rightTestSize one_le_rightTestSize)
open ComplexGodementParametric (continuous_continuedValue)
open ArchimedeanLocal (complexNormalizedAbs)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel

variable {r : ℕ}
local notation "m" => r + 1
local notation "n" => r + 1 + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "U" => Matrix.unitaryGroup (Fin n) ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Col" => Fin m → ℂ
local notation "κ" => (Measure.haar : Measure U)

private def rightAction : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] (Rect →L[ℝ] Rect) where
  toFun A := (mulRightLinearMap (Fin m) ℝ A).toContinuousLinearMap
  map_add' A B := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_add X A B)
  map_smul' c A := by ext X i j; exact congrArg (fun M : Rect => M i j) (Matrix.mul_smul X c A)

private def rightPullback (k : U) : Rect →L[ℝ] Rect := rightAction k.val

private theorem continuous_rightPullback : Continuous (rightPullback (r := r)) :=
  rightAction.toContinuousLinearMap.continuous.comp continuous_subtype_val

private theorem rightPullback_inverse (k : U) (X : Rect) :
    rightPullback k⁻¹ (rightPullback k X) = X := by
  change (X * (Unitary.toUnits k : G).val) * (Unitary.toUnits k⁻¹ : G).val = X
  rw [map_inv, Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]

private theorem exists_inverseBound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : Rect, ∀ k : U, ‖X‖ ≤ C * ‖rightPullback k X‖ := by
  have hinv : Continuous (fun k : U => (k⁻¹ : U)) := continuous_inv
  have hc := (continuous_rightPullback (r := r)).comp hinv
  obtain ⟨B, hB⟩ := (isCompact_univ.image hc.norm).bddAbove
  refine ⟨max B 0, le_max_right _ _, fun X k => ?_⟩
  have hb : ‖rightPullback k⁻¹‖ ≤ max B 0 :=
    (hB ⟨k, mem_univ _, rfl⟩).trans (le_max_left _ _)
  conv_lhs => rw [← rightPullback_inverse k X]
  exact ((rightPullback k⁻¹).le_opNorm _).trans (mul_le_mul_of_nonneg_right hb (norm_nonneg _))

private def averageTest (Φ : 𝓢(Rect, ℂ)) (w : C(U, ℂ)) : 𝓢(Rect, ℂ) :=
  Langlands.Analysis.SchwartzCompactAverage.average w rightPullback Φ κ
    w.continuous continuous_rightPullback (Classical.choose_spec exists_inverseBound).1
    (Classical.choose_spec exists_inverseBound).2

private theorem averageTest_apply (Φ : 𝓢(Rect, ℂ)) (w : C(U, ℂ)) (X : Rect) :
    averageTest Φ w X = ∫ k : U, w k * Φ (X * k.val) ∂κ := rfl

private def saturatedSupport (Φ : 𝓢(Rect, ℂ)) : Set Rect :=
  (fun p : Rect × U => p.1 * p.2⁻¹.val) '' (tsupport Φ ×ˢ univ)

private theorem isCompact_saturatedSupport (Φ : 𝓢(Rect, ℂ)) (hΦ : HasCompactSupport Φ) :
    IsCompact (saturatedSupport Φ) :=
  (hΦ.prod isCompact_univ).image (continuous_fst.matrix_mul
    (continuous_subtype_val.comp continuous_snd.inv))

private theorem mem_saturatedSupport {Φ : 𝓢(Rect, ℂ)} {X : Rect} {k : U}
    (h : Φ (rightPullback k X) ≠ 0) : X ∈ saturatedSupport Φ :=
  ⟨(rightPullback k X, k), ⟨subset_tsupport Φ h, mem_univ _⟩, rightPullback_inverse k X⟩

private theorem support_averageTest {Φ : 𝓢(Rect, ℂ)} (hΦ : HasCompactSupport Φ)
    (w : C(U, ℂ)) : tsupport (averageTest Φ w) ⊆ saturatedSupport Φ := by
  apply closure_minimal _ (isCompact_saturatedSupport Φ hΦ).isClosed
  intro X hX
  by_contra hn
  apply hX
  rw [averageTest_apply]
  exact integral_eq_zero_of_ae (ae_of_all _ fun k => by
    have hk : Φ (X * k.val) = 0 := by
      by_contra hk
      exact hn (mem_saturatedSupport (k := k) hk)
    change w k * Φ (X * k.val) = 0
    rw [hk, mul_zero])

private theorem saturatedSupport_fullRank {Φ : 𝓢(Rect, ℂ)}
    (hΦ : ∀ X ∈ tsupport Φ, HasFullRowRank X) : ∀ X ∈ saturatedSupport Φ, HasFullRowRank X := by
  rintro _ ⟨⟨X, k⟩, ⟨hX, _⟩, rfl⟩
  obtain ⟨Y, hY⟩ := hΦ X hX
  refine ⟨k.val * Y, ?_⟩
  have hk : k⁻¹.val * k.val = 1 := Units.inv_mul (Unitary.toUnits k)
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc k⁻¹.val, hk, Matrix.one_mul, hY]

private def weightedIntegral (Φ : 𝓢(Rect, ℂ)) (w : U → U → ℂ) (k : U) (X : Rect) : ℂ :=
  ∫ v : U, w k v * Φ (X * v.val) ∂κ

private theorem weightedIntegral_finite (Φ : 𝓢(Rect, ℂ)) {w : U → U → ℂ}
    (hw : w ∈ separated n) : (∀ k, Continuous (w k)) ∧
      ∃ S : Submodule ℂ (Rect → ℂ), FiniteDimensional ℂ S ∧ ∀ k, weightedIntegral Φ w k ∈ S := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨α, _, β, rfl⟩ := hw
    let f : Rect → ℂ := fun X => ∫ v : U, β v * Φ (X * v.val) ∂κ
    refine ⟨fun k => continuous_const.mul β.continuous, ℂ ∙ f, inferInstance, fun k => ?_⟩
    have he : weightedIntegral Φ (fun k v => α k * β v) k = α k • f := by
      funext X
      simp only [weightedIntegral, mul_assoc, integral_const_mul, Pi.smul_apply, smul_eq_mul, f]
    rw [he]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self f)
  | zero =>
    refine ⟨fun _ => continuous_const, ⊥, inferInstance, fun k => ?_⟩
    rw [Submodule.mem_bot]
    funext X
    simp [weightedIntegral]
  | add w v _ _ hw hv =>
    obtain ⟨hwc, S, hS, hwS⟩ := hw
    obtain ⟨hvc, T, hT, hvT⟩ := hv
    let : FiniteDimensional ℂ S := hS
    let : FiniteDimensional ℂ T := hT
    refine ⟨fun k => (hwc k).add (hvc k), S ⊔ T, inferInstance, fun k => ?_⟩
    have he : weightedIntegral Φ (w + v) k = weightedIntegral Φ w k + weightedIntegral Φ v k := by
      funext X
      have hΦc : Continuous (fun u : U => Φ (X * u.val)) :=
        Φ.continuous.comp (continuous_const.matrix_mul continuous_subtype_val)
      simp only [weightedIntegral, Pi.add_apply, add_mul]
      exact integral_add (integrable_of_continuous κ ((hwc k).mul hΦc))
        (integrable_of_continuous κ ((hvc k).mul hΦc))
    rw [he]
    have hl : S ≤ S ⊔ T := le_sup_left
    have hr : T ≤ S ⊔ T := le_sup_right
    exact Submodule.add_mem _ (hl (hwS k)) (hr (hvT k))
  | smul c w _ hw =>
    obtain ⟨hwc, S, hS, hwS⟩ := hw
    refine ⟨fun k => (hwc k).const_smul c, S, hS, fun k => ?_⟩
    have he : weightedIntegral Φ (c • w) k = c • weightedIntegral Φ w k := by
      funext X
      simp only [weightedIntegral, Pi.smul_apply, smul_eq_mul, mul_assoc, integral_const_mul]
    rw [he]
    exact Submodule.smul_mem _ _ (hwS k)

private theorem averageTest_finite (Φ : 𝓢(Rect, ℂ)) {w : C(U, ℂ)} (hw : w ∈ polynomialStar n) :
    FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ n =>
      translateTest k.val (averageTest Φ w))) := by
  have hw' : w ∈ (polynomialStar n).toSubalgebra := hw
  rw [polynomialStar_toSubalgebra] at hw'
  obtain ⟨_, S, hS, hs⟩ := weightedIntegral_finite Φ (inv_mul_mem_separated hw')
  let : FiniteDimensional ℂ S := hS
  apply Submodule.finiteDimensional_of_le (S₂ := S)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let u : U := ⟨k.val.val, k.2⟩
  have he : translateTest k.val (averageTest Φ w) = weightedIntegral Φ (fun u v => w (u⁻¹ * v)) u := by
    funext X
    change averageTest Φ w (X * u.val) = ∫ v : U, w (u⁻¹ * v) * Φ (X * v.val) ∂κ
    rw [averageTest_apply, ← integral_mul_left_eq_self (fun v : U => w (u⁻¹ * v) * Φ (X * v.val)) u]
    apply integral_congr_ae (ae_of_all _ fun v => ?_)
    change w v * Φ ((X * u.val) * v.val) = w (u⁻¹ * (u * v)) * Φ (X * (u * v).val)
    rw [inv_mul_cancel_left, Matrix.UnitaryGroup.mul_val, Matrix.mul_assoc]
  change translateTest k.val (averageTest Φ w) ∈ S
  rw [he]
  exact hs u

private def columnPoint (h : H) (v : Col) : Rect := rectangularJoin h.val (h.val.mulVec v)

private theorem continuous_columnPoint : Continuous (fun q : H × Col => columnPoint q.1 q.2) :=
  continuous_rectangularJoin.comp ((Units.continuous_val.comp continuous_fst).prodMk
    ((Units.continuous_val.comp continuous_fst).matrix_mulVec continuous_snd))

private theorem columnIntegral_average (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (Φ : 𝓢(Rect, ℂ)) (hΦ : HasCompactSupport Φ) (w : C(U, ℂ)) (h : H) :
    columnIntegral (complexScaledCharacter a) μ (averageTest Φ w) h =
      ∫ k : U, w k * columnIntegral (complexScaledCharacter a) μ (rightTest (Unitary.toUnits k) Φ) h ∂κ := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let η := rowMeasure μ m
  let ψ := complexScaledCharacter a
  let F (q : Col × U) : ℂ := w q.2 * Φ (columnPoint h q.1 * q.2.val) * ψ.complex (q.1 (Fin.last r))
  have hF : Continuous F := ((w.continuous.comp continuous_snd).mul (Φ.continuous.comp
    ((continuous_columnPoint.comp (continuous_const.prodMk continuous_fst)).matrix_mul
      (continuous_subtype_val.comp continuous_snd)))).mul
        (ψ.continuous_complex.comp ((continuous_apply _).comp continuous_fst))
  let p (X : Rect) : Col := h⁻¹.val.mulVec (rectangularLastColumn X)
  have hp : Continuous p := continuous_const.matrix_mulVec continuous_rectangularLastColumn
  have hP : IsCompact ((p '' saturatedSupport Φ) ×ˢ (univ : Set U)) :=
    ((isCompact_saturatedSupport Φ hΦ).image hp).prod isCompact_univ
  have hFc : HasCompactSupport F := HasCompactSupport.of_support_subset_isCompact hP (by
    intro q hq
    have hq' : Φ (columnPoint h q.1 * q.2.val) ≠ 0 := fun hz => hq (by simp [F, hz])
    refine ⟨⟨columnPoint h q.1, mem_saturatedSupport (k := q.2) hq', ?_⟩, mem_univ _⟩
    simp [p, columnPoint, Matrix.mulVec_mulVec])
  have hint : Integrable F (η.prod κ) := hF.integrable_of_hasCompactSupport hFc
  unfold columnIntegral
  change (∫ v, averageTest Φ w (columnPoint h v) * ψ.complex (v (Fin.last r)) ∂η) = _
  simp_rw [averageTest_apply, ← integral_mul_const]
  calc
    _ = ∫ v, ∫ k, F (v, k) ∂κ ∂η := rfl
    _ = ∫ k, ∫ v, F (v, k) ∂η ∂κ := integral_integral_swap hint
    _ = _ := by
      apply integral_congr_ae (ae_of_all _ fun k => ?_)
      rw [← integral_const_mul]
      apply integral_congr_ae (ae_of_all _ fun v => ?_)
      change (w k * Φ (columnPoint h v * k.val)) * ψ.complex (v (Fin.last r)) =
        w k * (Φ (columnPoint h v * k.val) * ψ.complex (v (Fin.last r)))
      exact mul_assoc _ _ _

private theorem iteratedKernel_average (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (hΦ : HasCompactSupport Φ) (w : C(U, ℂ))
    (W : H → ℂ) (t : ℂ) (h : H) :
    iteratedKernel (complexScaledCharacter a) μ d (averageTest Φ w) W t h =
      ∫ k : U, w k * iteratedKernel (complexScaledCharacter a) μ d
        (rightTest (Unitary.toUnits k) Φ) W t h ∂κ := by
  unfold iteratedKernel
  rw [columnIntegral_average μ a Φ hΦ, ← integral_mul_const, ← integral_mul_const, ← integral_mul_const]
  exact integral_congr_ae (ae_of_all _ fun k => by ring)

private theorem continuous_detPower {j : ℕ} (s : ℂ) :
    Continuous (fun g : Langlands.GeneralLinear j ℂ => ArchimedeanLocal.detPower complexNormalizedAbs g s) := by
  have hlog : Continuous (fun g : Langlands.GeneralLinear j ℂ =>
      Real.log (complexNormalizedAbs g.val.det)) :=
    (Units.continuous_val.matrix_det.norm.pow 2).log fun g =>
      (pow_pos (norm_pos_iff.mpr (Matrix.GeneralLinearGroup.det_ne_zero g)) 2).ne'
  exact ((Complex.continuous_ofReal.comp hlog).const_mul s).cexp

private theorem stronglyMeasurable_translatedKernel (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : H → ℂ) (hW : Continuous W) (t : ℂ) :
    StronglyMeasurable (fun q : H × U => iteratedKernel (complexScaledCharacter a) μ d
      (rightTest (Unitary.toUnits q.2) Φ) W t q.1) := by
  let : μ.measure.IsAddHaarMeasure := μ.isAddHaar
  let F (x : (H × U) × Col) : ℂ := Φ (columnPoint x.1.1 x.2 * x.1.2.val) *
    (complexScaledCharacter a).complex (x.2 (Fin.last r))
  have hF : Continuous F := (Φ.continuous.comp
    ((continuous_columnPoint.comp ((continuous_fst.comp continuous_fst).prodMk continuous_snd)).matrix_mul
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))).mul
        ((complexScaledCharacter a).continuous_complex.comp ((continuous_apply _).comp continuous_snd))
  have hcol : StronglyMeasurable (fun q : H × U =>
      columnIntegral (complexScaledCharacter a) μ (rightTest (Unitary.toUnits q.2) Φ) q.1) :=
    hF.stronglyMeasurable.integral_prod_right' (ν := rowMeasure μ m)
  have hχ : Continuous (fun q : H × U => (d.character (determinant q.1) : ℂ)) :=
    Units.continuous_val.comp (d.character.continuous.comp
      (Langlands.GeneralLinear.determinantContinuous.continuous.comp continuous_fst))
  exact ((hcol.mul (hW.comp continuous_fst.inv).stronglyMeasurable).mul hχ.stronglyMeasurable).mul
    ((continuous_detPower t).comp continuous_fst).stronglyMeasurable

private theorem integral_iteratedKernel_average {P : Type} (ν : Measure H)
    [ν.IsHaarMeasure] [SFinite ν] (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    (S : Set P) (W : P → H → ℂ) (hWc : ∀ p ∈ S, Continuous (W p))
    (hWb : HasUniformSimpleRootBound S W) (p : P) (hp : p ∈ S) (t : ℂ)
    (Φ : 𝓢(Rect, ℂ)) (hΦ : HasCompactSupport Φ) (w : C(U, ℂ)) :
    (∫ h, iteratedKernel (complexScaledCharacter a) μ d (averageTest Φ w) (W p) t h ∂ν) =
      ∫ k : U, w k * ∫ h, iteratedKernel (complexScaledCharacter a) μ d
        (rightTest (Unitary.toUnits k) Φ) (W p) t h ∂ν ∂κ := by
  obtain ⟨I, N, B, hBi, hB₀, hb⟩ :=
    complexGodementTranslatedBounds ν μ a d S W hWc hWb |(t - 1).re| (abs_nonneg _)
  obtain ⟨R, hR⟩ := isCompact_univ.exists_bound_of_continuousOn
    ((continuous_rightTestSize (r := r)).comp continuous_unitary_toUnits).continuousOn
  obtain ⟨A, hA⟩ := isCompact_univ.exists_bound_of_continuousOn w.continuous.continuousOn
  let C := I.sup (schwartzSeminormFamily ℝ Rect ℂ) Φ
  let F (q : H × U) := w q.2 * iteratedKernel (complexScaledCharacter a) μ d
    (rightTest (Unitary.toUnits q.2) Φ) (W p) t q.1
  have hFm : StronglyMeasurable F :=
    (w.continuous.comp continuous_snd).stronglyMeasurable.mul
      (stronglyMeasurable_translatedKernel μ a d Φ (W p) (hWc p hp) t)
  have hF : Integrable F (ν.prod κ) := by
    refine (((hBi.mul_const (max A 0 * max R 1 ^ N * C)).comp_fst κ).mono'
      hFm.aestronglyMeasurable (ae_of_all _ fun q => ?_))
    have hsize : rightTestSize (Unitary.toUnits q.2) ≤ max R 1 :=
      (Real.le_norm_self _).trans ((hR q.2 (mem_univ _)).trans (le_max_left _ _))
    have hsize₀ := zero_le_one.trans (one_le_rightTestSize (Unitary.toUnits q.2))
    have hWA : ‖w q.2‖ ≤ max A 0 := (hA q.2 (mem_univ _)).trans (le_max_left _ _)
    have hC : 0 ≤ C := apply_nonneg _ _
    calc
      ‖F q‖ ≤ max A 0 * (B q.1 * rightTestSize (Unitary.toUnits q.2) ^ N * C) := by
        dsimp only [F]
        rw [norm_mul]
        exact mul_le_mul hWA ((hb p hp t le_rfl (Unitary.toUnits q.2) Φ).2.1 q.1)
          (norm_nonneg _) (le_max_right _ _)
      _ ≤ max A 0 * (B q.1 * max R 1 ^ N * C) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hsize₀ hsize N) (hB₀ q.1)) hC)
          (le_max_right _ _)
      _ = B q.1 * (max A 0 * max R 1 ^ N * C) := by ring
  simp_rw [iteratedKernel_average μ a d Φ hΦ w]
  calc
    _ = ∫ h, ∫ k, F (h, k) ∂κ ∂ν := rfl
    _ = ∫ k, ∫ h, F (h, k) ∂ν ∂κ := integral_integral_swap hF
    _ = _ := integral_congr_ae (ae_of_all _ fun k => integral_const_mul (w k) _)

private theorem rightTest_one (Φ : 𝓢(Rect, ℂ)) : rightTest (1 : G) Φ = Φ := by
  ext X
  simp [rightTest_apply]

private theorem continuedValue_one (ν : Measure H) (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (d : ComplexCharacterData) (Φ : 𝓢(Rect, ℂ)) (W : H → ℂ) (s : ℂ) :
    continuedValue ν μ d a Φ W 1 s = (d.character ((-1 : ℂˣ) ^ m) : ℂ) *
      ∫ h, iteratedKernel (complexScaledCharacter a) μ d Φ W ((((m : ℕ) + 1 : ℂ) / 2) + s) h ∂ν := by
  rw [continuedValue, rightTest_one, map_one, map_one, mul_one]
  have h : ArchimedeanLocal.detPower complexNormalizedAbs (1 : G) s = 1 := by
    simp [ArchimedeanLocal.detPower, complexNormalizedAbs]
  rw [h, mul_one]

/-- A nonzero continued Godement value at the identity is attained on a compact full-row-rank
Schwartz test with finite unitary orbit. -/
def ComplexGodementFiniteOrbitNonzeroStatement : Prop :=
  ∀ {P : Type} (ν : Measure H) [ν.IsHaarMeasure] [SFinite ν]
    (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (d : ComplexCharacterData)
    (S : Set P) (W : P → H → ℂ), (∀ p ∈ S, Continuous (W p)) → HasUniformSimpleRootBound S W →
    ∀ p ∈ S, ∀ s : ℂ, (∃ g, W p g ≠ 0) →
    ∃ Φ : 𝓢(Rect, ℂ), HasCompactSupport Φ ∧ (∀ X ∈ tsupport Φ, HasFullRowRank X) ∧
      FiniteDimensional ℂ (Submodule.span ℂ (range fun k : unitaryCompact ℂ n => translateTest k.val Φ)) ∧
      continuedValue ν μ d a Φ (W p) 1 s ≠ 0

set_option maxHeartbeats 800000 in
theorem complexGodementFiniteOrbitNonzero : ComplexGodementFiniteOrbitNonzeroStatement (r := r) := by
  intro P ν hν hνf μ a d S W hWc hWb p hp s hWnz
  obtain ⟨Φ, hΦ, hfull, hΦnz⟩ := complexGodementLocalizedNonzero ν μ a d s (W p) (hWc p hp) hWnz
  let t : ℂ := (((m : ℕ) + 1 : ℂ) / 2) + s
  let B (k : U) : ℂ := ∫ h, iteratedKernel (complexScaledCharacter a) μ d
        (rightTest (Unitary.toUnits k) Φ) (W p) t h ∂ν
  have hB₁ : B 1 ≠ 0 := by
    rw [continuedValue_one] at hΦnz
    simpa only [B, map_one, rightTest_one] using right_ne_zero_of_mul hΦnz
  let c : ℂ := d.character ((-1 : ℂˣ) ^ m)
  let b : ℂ := ((m : ℕ) : ℂ) / 2
  let A (g : G) := c * characterWeight d b (determinant g) * ArchimedeanLocal.detPower complexNormalizedAbs g s
  have hAnz (g : G) : A g ≠ 0 := by
    apply mul_ne_zero _ (Complex.exp_ne_zero _)
    exact mul_ne_zero (d.character _).ne_zero
      (mul_ne_zero (d.character _).ne_zero (Complex.cpow_ne_zero_iff.mpr
        (Or.inl (normSqC_ne_zero (determinant g).ne_zero))))
  have hAc : Continuous A :=
    ((continuous_characterWeight d b).comp Langlands.GeneralLinear.determinantContinuous.continuous
      |>.const_mul c).mul (continuous_detPower s)
  have hB : Continuous B := by
    have he (k : U) : B k = continuedValue ν μ d a Φ (W p) (Unitary.toUnits k) s / A (Unitary.toUnits k) := by
      rw [eq_div_iff (hAnz _), continuedValue]
      exact mul_comm _ _
    rw [funext he]
    exact ((continuous_continuedValue ν μ a d S W hWc hWb p hp Φ s).comp continuous_unitary_toUnits).div
      (hAc.comp continuous_unitary_toUnits) fun k => hAnz (Unitary.toUnits k)
  by_contra! hn
  have hzero := eq_zero_of_integral_polynomial_mul_eq_zero κ ⟨B, hB⟩ (by
    intro w hw
    have hsub := support_averageTest hΦ w
    have hn' := hn (averageTest Φ w)
      ((isCompact_saturatedSupport Φ hΦ).of_isClosed_subset (isClosed_tsupport _) hsub)
      (fun X hX => saturatedSupport_fullRank hfull X (hsub hX)) (averageTest_finite Φ hw)
    rw [continuedValue_one, integral_iteratedKernel_average ν μ a d S W hWc hWb p hp _ Φ hΦ w] at hn'
    exact (mul_eq_zero.mp hn').resolve_left (d.character _).ne_zero)
  exact hB₁ (congrArg (fun f : C(U, ℂ) => f 1) hzero)

end Langlands.Global.RankinSelbergGlobal.ComplexGodementAddedCharacter
