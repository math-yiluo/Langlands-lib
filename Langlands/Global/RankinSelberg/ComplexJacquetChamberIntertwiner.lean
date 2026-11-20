import Langlands.Global.RankinSelberg.ComplexJacquetChamberSmooth
import Langlands.Global.RankinSelberg.ComplexGodementStandardGrowth

/-! # The complex open-cell Jacquet intertwiner on the strict chamber -/

noncomputable section

open MeasureTheory
open scoped Manifold

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberIntertwiner

open Langlands.Archimedean (complexStandardModule complexPositionCharacter unitaryCompact)
open Langlands.Archimedean.ComplexGramFormula (complexPositionExponent norm_phaseUnit)
open Langlands.Archimedean.ComplexDuality (isCompact_unitaryCompact)
open Langlands.Archimedean.ComplexPartialJacquet (IsPhasePower IsStrictlyDominant)
open Langlands.Archimedean.ComplexStrictLanglandsQuotient (isPhasePower)
open Langlands.GeneralLinear (weylLong weylLong_mul_self inverseTranspose)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure UnitaryAdditiveCharacter)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData complexScaledCharacter complexScaledCharacter_apply)
open ComplexGodement (exists_height_bound_standard)
open ComplexGodementJacquetComparison (openCellIntegral)
open ComplexJacquetUnipotentMeasure (entryHaar entryHaar_isHaar transposeReflection
  transposeReflection_eq measurePreserving_transposeReflection)
open ComplexJacquetChamberConvergence (radialChar sphericalMajorant sphericalMajorant_mem
  complexJacquetOpenCellConvergence norm_mul_le_sphericalMajorant)
open ComplexJacquetChamberSmooth (contMDiff_openCellIntegral rightDerivative_openCellIntegral)

attribute [local instance] ArchimedeanLocal.archimedeanComplexGLMeasurable
  ArchimedeanLocal.archimedeanComplexGLBorel ArchimedeanLocal.archimedeanComplexNMeasurable
  ArchimedeanLocal.archimedeanComplexNBorel

variable {r : ℕ}
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "N" => GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "w" => weylLong (r + 1) ℂ

private theorem transposeReflection_mul (u v : N) :
    transposeReflection (r + 1) (u * v) = transposeReflection (r + 1) v * transposeReflection (r + 1) u := by
  apply Subtype.ext
  simp only [transposeReflection_eq, Whittaker.reflectedUnipotent_val, Subgroup.coe_inv, Subgroup.coe_mul,
    mul_inv_rev, map_mul, mul_assoc]
  rw [← mul_assoc w w, weylLong_mul_self, one_mul]

/-- The entry measure is also right invariant by the measure-preserving transpose reflection. -/
theorem entryHaar_isMulRightInvariant (μ : AdditiveHaarMeasure ℂ) (r : ℕ) :
    (entryHaar μ (r + 1)).IsMulRightInvariant := by
  let ν := entryHaar μ (r + 1)
  have : ν.IsHaarMeasure := entryHaar_isHaar μ (r + 1)
  let e := transposeReflection (r + 1)
  have hp : MeasurePreserving e ν ν := measurePreserving_transposeReflection μ (r + 1)
  refine ⟨fun a => ?_⟩
  have h : (fun u : GeneralLinear.upperUnipotent (r + 1) ℂ => u * a) =
      e.symm ∘ (fun v => e a * v) ∘ e := by
    funext u
    change u * a = e.symm (e a * e u)
    rw [← transposeReflection_mul, e.symm_apply_apply]
  rw [h]
  exact ((hp.symm e).comp ((measurePreserving_mul_left ν (e a)).comp hp)).map_eq

private theorem whittakerCharacter_mul (a : ℂˣ) (u v : N) :
    complexWhittakerCharacter a (u * v).val =
      complexWhittakerCharacter a u.val * complexWhittakerCharacter a v.val := by
  simp only [complexWhittakerCharacter, GeneralLinear.UpperUnipotent.mul_adjacent_entry,
    Finset.sum_add_distrib, AddChar.map_add_eq_mul]

private theorem whittakerCharacter_inv (a : ℂˣ) (u : N) :
    complexWhittakerCharacter a (u⁻¹).val = complexWhittakerCharacter (-a) u.val := by
  simp only [complexWhittakerCharacter, GeneralLinear.UpperUnipotent.inv_adjacent_entry,
    Finset.sum_neg_distrib, UnitaryAdditiveCharacter.complex_apply, complexScaledCharacter_apply,
    Units.val_neg, neg_mul, mul_neg]

/-- The positive integrating character gives the inverse left character of the open-cell function. -/
theorem openCellIntegral_left_mul (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (f : G → ℂ) (u : N) (g : G) :
    openCellIntegral a (entryHaar μ (r + 1)) f (u.val * g) =
      complexWhittakerCharacter (-a) u.val * openCellIntegral a (entryHaar μ (r + 1)) f g := by
  let ν := entryHaar μ (r + 1)
  have : ν.IsMulRightInvariant := entryHaar_isMulRightInvariant μ r
  let F (v : N) := f (w * v.val * g) * complexWhittakerCharacter a (v * u⁻¹).val
  calc
    _ = ∫ v, F (v * u) ∂ν := by
      unfold openCellIntegral
      apply integral_congr_ae (ae_of_all _ fun v => ?_)
      dsimp only [F]
      rw [mul_inv_cancel_right, Subgroup.coe_mul, mul_assoc w, mul_assoc w, mul_assoc]
    _ = ∫ v, F v ∂ν := integral_mul_right_eq_self F u
    _ = _ := by
      unfold F openCellIntegral
      simp_rw [whittakerCharacter_mul, whittakerCharacter_inv, ← mul_assoc]
      rw [integral_mul_const, mul_comm]

private theorem integrable_openCellKernel (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) (g : G) :
    Integrable (fun u : N => f (w * u.val * g) * complexWhittakerCharacter a u.val)
      (entryHaar μ (r + 1)) := by
  have h := complexJacquetOpenCellConvergence r μ _ _ (isPhasePower ds) he f hf g
  have hθ : Continuous (fun u : N => complexWhittakerCharacter a u.val) := by
    unfold complexWhittakerCharacter
    exact (complexScaledCharacter a).continuous_complex.comp
      (continuous_finsetSum _ fun i _ => (GeneralLinear.UpperUnipotent.entry i.castSucc i.succ).continuous)
  refine h.norm.mono' (h.aestronglyMeasurable.mul hθ.aestronglyMeasurable) (ae_of_all _ fun u => ?_)
  simp [complexWhittakerCharacter]

section Height

open scoped Matrix.Norms.Frobenius
open ComplexPlaceAnalytic (complexMatrixHeight_eq_frobenius)

private theorem continuous_height : Continuous (complexMatrixHeight (n := r + 1)) := by
  simp only [funext complexMatrixHeight_eq_frobenius]
  exact (Units.continuous_val.norm.pow 2).add ((Units.continuous_val.comp continuous_inv).norm.pow 2)

private theorem height_nonneg (g : G) : 0 ≤ complexMatrixHeight g := by
  rw [complexMatrixHeight_eq_frobenius]
  positivity

private theorem height_mul_le (g h : G) : complexMatrixHeight (g * h) ≤ complexMatrixHeight g * complexMatrixHeight h := by
  simp only [complexMatrixHeight_eq_frobenius, Units.val_mul, mul_inv_rev]
  calc
    _ ≤ (‖g.val‖ * ‖h.val‖) ^ 2 + (‖h⁻¹.val‖ * ‖g⁻¹.val‖) ^ 2 :=
      add_le_add (pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) _)
        (pow_le_pow_left₀ (norm_nonneg _) (norm_mul_le _ _) _)
    _ ≤ _ := by
      simp only [mul_pow]
      nlinarith [mul_nonneg (sq_nonneg ‖g.val‖) (sq_nonneg ‖h⁻¹.val‖),
        mul_nonneg (sq_nonneg ‖g⁻¹.val‖) (sq_nonneg ‖h.val‖)]

end Height

private theorem integrable_sphericalMajorant (μ : AdditiveHaarMeasure ℂ) (t : ℕ → ℝ)
    (he : IsStrictlyDominant (fun i => (t i : ℂ)) r) :
    Integrable (fun u : N => ‖sphericalMajorant (r + 1) t (w * u.val)‖) (entryHaar μ (r + 1)) := by
  have hrad : IsPhasePower (radialChar t) (fun i => (t i : ℂ)) := {
    eq := by intro i z; simp [radialChar, norm_phaseUnit]
    one := by intro i; simp [radialChar]
    norm_phase := by intro i z; simp [radialChar, norm_phaseUnit] }
  simpa only [mul_one] using (complexJacquetOpenCellConvergence r μ _ _ hrad he _
    (sphericalMajorant_mem (r + 1) t).1 1).norm

private theorem openCellIntegral_moderateGrowth (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (hds : ds.length = r + 1) (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    {f : G → ℂ} (hf : f ∈ complexStandardModule (r + 1) ds) :
    ∃ (C : ℝ) (M : ℕ), ∀ g : G,
      ‖openCellIntegral a (entryHaar μ (r + 1)) f g‖ ≤ C * complexMatrixHeight g ^ M := by
  obtain ⟨M, hM⟩ := exists_height_bound_standard (Nat.succ_pos r) ds hds
  obtain ⟨C, hC, hF⟩ := hM f hf
  obtain ⟨D₀, hD₀⟩ := (isCompact_unitaryCompact (r + 1)).exists_bound_of_continuousOn
    continuous_height.continuousOn
  let D := max D₀ 0
  have hD : 0 ≤ D := le_max_right _ _
  have hbound (g k : G) (hk : k ∈ unitaryCompact ℂ (r + 1)) :
      ‖f (k * g)‖ ≤ C * D ^ M * complexMatrixHeight g ^ M := by
    have hkD : complexMatrixHeight k ≤ D := by
      have h := hD₀ k hk
      rw [Real.norm_of_nonneg (height_nonneg k)] at h
      exact h.trans (le_max_left _ _)
    have hg : complexMatrixHeight (k * g) ≤ D * complexMatrixHeight g :=
      (height_mul_le k g).trans (mul_le_mul_of_nonneg_right hkD (height_nonneg g))
    calc
      _ ≤ C * (D * complexMatrixHeight g) ^ M :=
        (hF _).trans (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (height_nonneg _) hg _) hC)
      _ = _ := by rw [mul_pow, mul_assoc]
  let t : ℕ → ℝ := fun i => (complexPositionExponent ds i).re
  let P (u : N) := ‖sphericalMajorant (r + 1) t (w * u.val)‖
  let ν := entryHaar μ (r + 1)
  have hdom : IsStrictlyDominant (fun i => (t i : ℂ)) r := by
    simpa only [IsStrictlyDominant, Complex.ofReal_re, t] using he
  have hP : Integrable P ν := integrable_sphericalMajorant μ t hdom
  refine ⟨C * D ^ M * (∫ u, P u ∂ν), M, fun g => ?_⟩
  calc
    _ ≤ ∫ u, (C * D ^ M * complexMatrixHeight g ^ M) * P u ∂ν := by
      unfold openCellIntegral
      apply norm_integral_le_of_norm_le (hP.const_mul _)
      exact ae_of_all _ fun u => by
        simp only [norm_mul, show ‖complexWhittakerCharacter a u.val‖ = 1 by
          simp [complexWhittakerCharacter], mul_one]
        exact norm_mul_le_sphericalMajorant (isPhasePower ds) hf.2 g (hbound g) (w * u.val)
    _ = _ := by rw [integral_const_mul]; ring

open scoped Matrix.Norms.Operator in
/-- The linear open-cell Jacquet map on compact-finite inducing functions in the chamber. -/
def chamberIntertwiner (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r) :
    Automorphic.complexStandardKFinite (r + 1) ds →ₗ[ℂ] (G → ℂ) where
  toFun f := openCellIntegral a (entryHaar μ (r + 1)) f.val
  map_add' f h := by
    funext g
    unfold openCellIntegral
    simp only [Pi.add_apply, Submodule.coe_add, add_mul]
    exact integral_add (integrable_openCellKernel μ ds a he f.2.1 g)
      (integrable_openCellKernel μ ds a he h.2.1 g)
  map_smul' c f := by
    funext g
    unfold openCellIntegral
    simp only [RingHom.id_apply, Pi.smul_apply, Submodule.coe_smul, smul_eq_mul, mul_assoc,
      integral_const_mul]

open scoped Matrix.Norms.Operator in
theorem isComplexWhittakerIntertwiner_chamberIntertwiner
    (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData) (hds : ds.length = r + 1)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r) :
    IsComplexWhittakerIntertwiner r ds (-a) (chamberIntertwiner μ ds a he) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro f u hu g
    exact openCellIntegral_left_mul μ a f.val ⟨u, hu⟩ g
  · intro f
    exact contMDiff_openCellIntegral μ ds a he f.2.1
  · intro f
    exact openCellIntegral_moderateGrowth μ ds hds a he f.2.1
  · intro k f f' h
    change openCellIntegral a (entryHaar μ (r + 1)) f'.val = _
    rw [h]
    funext g
    unfold openCellIntegral
    apply integral_congr_ae (ae_of_all _ fun u => ?_)
    change f.val ((w * u.val * g) * k.val) * _ = f.val (w * u.val * (g * k.val)) * _
    rw [mul_assoc]
  · intro X f f' h
    exact (rightDerivative_openCellIntegral μ ds a he f.2.1 f'.2.1 X h).symm

open scoped Matrix.Norms.Operator in
/-- Every chamber open-cell value lies in the Library's exact Whittaker model. -/
theorem openCellIntegral_mem_complexWhittakerModel
    (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData) (hds : ds.length = r + 1)
    (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r)
    (f : Automorphic.complexStandardKFinite (r + 1) ds) :
    openCellIntegral a (entryHaar μ (r + 1)) f.val ∈ complexWhittakerModel r ds (-a) :=
  Submodule.mem_iSup_of_mem (chamberIntertwiner μ ds a he)
    (Submodule.mem_iSup_of_mem (isComplexWhittakerIntertwiner_chamberIntertwiner μ ds hds a he) ⟨f, rfl⟩)

open scoped Matrix.Norms.Operator in
variable (r) in
/-- The open-cell construction gives an actual Whittaker intertwiner in the strict chamber. -/
def ComplexJacquetChamberIntertwinerStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (ds : List ComplexCharacterData), ds.length = r + 1 →
    ∀ (a : ℂˣ) (he : IsStrictlyDominant (complexPositionExponent ds) r),
      IsComplexWhittakerIntertwiner r ds (-a) (chamberIntertwiner μ ds a he)

theorem complexJacquetChamberIntertwiner : ComplexJacquetChamberIntertwinerStatement r :=
  isComplexWhittakerIntertwiner_chamberIntertwiner

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetChamberIntertwiner
