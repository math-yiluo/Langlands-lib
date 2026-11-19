import Langlands.Global.RankinSelberg.ComplexGodementDiagonal
import Langlands.Global.RankinSelberg.ComplexLocalIwasawaHaar
import Mathlib.MeasureTheory.Integral.Prod

/-! # Triangular integration of complex Godement sections -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped Matrix.Norms.Operator NNReal ENNReal

namespace Langlands.Global.RankinSelbergGlobal.ComplexGodement

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open ComplexLocalWhittakerGauge (logTorus)
open ComplexLocalIwasawa (logTorus_neg)
open ComplexLocalIwasawaHaar (complexIwasawaHaar)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

local instance triangularGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℂ) :=
  borel _
local instance triangularGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℂ) := ⟨rfl⟩
local instance triangularGLSecondCountable (n : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear n ℂ) :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

variable {n : ℕ}
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent n ℂ
local notation "K" => unitaryCompact ℂ n
local notation "Y" => (Fin n → ℝ)
local notation "X" => (UpperEntryPair n → ℂ)

private theorem entryCorrection_right_depends (a : N) (ij : UpperEntryPair n) (x z : X)
    (he : ∀ kl : UpperEntryPair n,
      kl.1.2.val - kl.1.1.val < ij.1.2.val - ij.1.1.val → x kl = z kl) :
    (upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) - x) ij =
      (upperEntryCoordinates n ((upperEntryCoordinates n).symm z * a) - z) ij := by
  simp only [Pi.sub_apply, upperEntryCoordinates_mul, Homeomorph.apply_symm_apply]
  have hs :
      (∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        x ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩) =
      ∑ k : {k : Fin n // ij.1.1 < k ∧ k < ij.1.2},
        z ⟨(ij.1.1, k), k.2.1⟩ * upperEntryCoordinates n a ⟨(k, ij.1.2), k.2.2⟩ := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [he ⟨(ij.1.1, k), k.2.1⟩]
    have hi : ij.1.1.val < k.val.val := k.2.1
    have hj : k.val.val < ij.1.2.val := k.2.2
    dsimp
    omega
  rw [hs]
  abel

private theorem upperEntry_rightTranslation_preserving (a : N) :
    MeasurePreserving (fun x : X => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a))
      volume volume := by
  let f : X → X := fun x => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) - x
  have hf : Continuous f :=
    ((upperEntryCoordinates n).continuous.comp
      ((upperEntryCoordinates n).symm.continuous.mul continuous_const)).sub continuous_id
  have hp := Langlands.HarmonicAnalysis.finiteTriangularTranslation
    (UpperEntryPair n) (fun _ => ℂ) (fun _ => volume)
    (fun ij => ij.1.2.val - ij.1.1.val) f hf.measurable (entryCorrection_right_depends a)
  have he : (fun x ij => f x ij + x ij) =
      fun x => upperEntryCoordinates n ((upperEntryCoordinates n).symm x * a) := by
    funext x ij
    exact sub_add_cancel _ _
  rw [he] at hp
  exact hp

private theorem rightInvariant_entryHaar :
    ((volume : Measure X).map (upperEntryCoordinates n).symm).IsMulRightInvariant := by
  let e : N ≃ₜ X := upperEntryCoordinates n
  refine ⟨fun a => ?_⟩
  have hp := upperEntry_rightTranslation_preserving a
  have he : (· * a) ∘ e.symm = e.symm ∘ (fun x => e (e.symm x * a)) := by
    funext x
    exact (e.symm_apply_apply _).symm
  rw [Measure.map_map (measurable_mul_const a) e.symm.measurable, he,
    ← Measure.map_map e.symm.measurable hp.measurable, hp.map_eq]

/-- The right Haar formula in unitary, unipotent, positive-diagonal order, with additive
Lebesgue measure in the unipotent entries and in the logarithmic diagonal coordinates. -/
theorem exists_rightIwasawa_entryMeasure (μ : Measure G) [μ.IsHaarMeasure]
    [μ.IsMulRightInvariant] (κ : Measure K) [κ.IsHaarMeasure] :
    ∃ c : ℝ≥0, 0 < c ∧ μ = c • Measure.map
      (fun p : (Y × X) × K => p.2.val * ((upperEntryCoordinates n).symm p.1.2).val * logTorus p.1.1)
      (((volume : Measure Y).prod (volume : Measure X)).prod κ) := by
  let e : N ≃ₜ X := upperEntryCoordinates n
  let ν : Measure N := (volume : Measure X).map e.symm
  have : ν.IsMulRightInvariant := rightInvariant_entryHaar
  have : IsFiniteMeasureOnCompacts ν := IsFiniteMeasureOnCompacts.map _ e.symm
  have : ν.IsOpenPosMeasure := e.symm.continuous.isOpenPosMeasure_map e.symm.surjective
  have : ν.inv.IsHaarMeasure := {}
  have : μ.inv.IsHaarMeasure := {}
  have : κ.IsMulRightInvariant := Langlands.CompactFactorization.isMulRightInvariant_of_compactSpace κ
  have : κ.inv.IsHaarMeasure := {}
  obtain ⟨c, hc, hμ⟩ := complexIwasawaHaar n μ.inv ν.inv κ.inv inferInstance inferInstance inferInstance
  let toG : (Y × N) × K → G := fun p => logTorus p.1.1 * p.1.2.val * p.2.val
  have htoG : Measurable toG :=
    ((ComplexLocalIwasawa.continuous_logTorus.measurable.comp (measurable_fst.comp measurable_fst)).mul
      (measurable_subtype_coe.comp (measurable_snd.comp measurable_fst))).mul
      (measurable_subtype_coe.comp measurable_snd)
  let source := ((volume : Measure Y).prod (volume : Measure X)).prod κ
  let changeCoordinates : (Y × X) × K → (Y × N) × K :=
    Prod.map (Prod.map Neg.neg (fun x => (e.symm x)⁻¹)) Inv.inv
  have hiN : MeasurePreserving Inv.inv ν ν.inv := ⟨measurable_inv, rfl⟩
  have hiK : MeasurePreserving Inv.inv κ κ.inv := ⟨measurable_inv, rfl⟩
  have he : MeasurePreserving e.symm volume ν := ⟨e.symm.measurable, rfl⟩
  have hx : MeasurePreserving changeCoordinates source ((volume.prod ν.inv).prod κ.inv) :=
    ((Measure.measurePreserving_neg (volume : Measure Y)).prod (hiN.comp he)).prod hiK
  refine ⟨c, hc, ?_⟩
  calc
    μ = μ.inv.inv := (Measure.inv_inv μ).symm
    _ = c • Measure.map (Inv.inv ∘ toG ∘ changeCoordinates) source := by
      rw [Measure.inv_def, hμ, Measure.map_smul _ measurable_inv.aemeasurable,
        ← hx.map_eq, Measure.map_map htoG hx.measurable,
        Measure.map_map measurable_inv (htoG.comp hx.measurable)]
    _ = _ := by
      congr 2
      funext p
      change (logTorus (-p.1.1) * (e.symm p.1.2).val⁻¹ * p.2.val⁻¹)⁻¹ = _
      rw [logTorus_neg, mul_inv_rev, mul_inv_rev, inv_inv, inv_inv, inv_inv, mul_assoc]

private def positiveDiagonalUnits (y : Y) : Fin n → ℂˣ :=
  fun i => Units.mk0 (Real.exp (y i) : ℂ) (Complex.ofReal_ne_zero.mpr (Real.exp_ne_zero _))

private theorem continuous_upperTriangularEntries (a : Fin n → ℂ) :
    Continuous (upperTriangularEntries a) := by
  apply continuous_matrix
  intro i j
  by_cases h : i < j
  · simp only [upperTriangularEntries, dite_eq_left h]
    exact continuous_apply (⟨(i, j), h⟩ : UpperEntryPair n)
  · simp only [upperTriangularEntries, dite_eq_right h]
    exact continuous_const

private theorem continuous_scaleUpperEntries (y : Y) : Continuous (scaleUpperEntries y) := by
  refine continuous_pi fun p => ?_
  change Continuous (fun x : X => Real.exp (y p.1.2) • x p)
  have hp : Continuous (fun x : X => x p) := continuous_apply p
  exact hp.const_smul (Real.exp (y p.1.2))

/-- The complex Godement integrand in additive triangular entries, after including the column
Jacobian. The integration measure for `y` and `z` is Lebesgue, where `y` is logarithmic. -/
def triangularGodementKernel (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : G → ℂ)
    (g : Langlands.GeneralLinear (n + 1) ℂ) (k : K) (y : Y) (z : X) : ℂ :=
  Φ (k.val.val * upperTriangularEntries (fun i => (Real.exp (y i) : ℂ)) z * trailingRows g.val) *
    (f k.val⁻¹ * (d.character (determinant k.val) : ℂ)) *
    diagonalTateWeight d ds (positiveDiagonalUnits y)

private theorem integral_triangular_entries (d : ComplexCharacterData) (ds : List ComplexCharacterData)
    (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (hΦ : Continuous Φ) {f : G → ℂ}
    (hf : f ∈ complexStandardModule n ds) (g : Langlands.GeneralLinear (n + 1) ℂ)
    (k : K) (y : Y) :
    (∫ x : X, godementSectionIntegrand d Φ f g
      (k.val * ((upperEntryCoordinates n).symm x).val * logTorus y)) =
      ∫ z : X, triangularGodementKernel d ds Φ f g k y z := by
  let J : ℂ := ((upperEntryJacobian y : ℝ) : ℂ)
  have hJ : J ≠ 0 := Complex.ofReal_ne_zero.mpr
    (show 0 < (upperEntryJacobian y : ℝ) from upperEntryJacobian_pos y).ne'
  let F := triangularGodementKernel d ds Φ f g k y
  have hmat : Continuous (fun z : X => k.val.val *
      upperTriangularEntries (fun i => (Real.exp (y i) : ℂ)) z * trailingRows g.val) :=
    ((continuous_const.matrix_mul (continuous_upperTriangularEntries _)).matrix_mul continuous_const)
  have hcont : Continuous F :=
    ((hΦ.comp hmat).mul continuous_const).mul continuous_const
  apply mul_left_cancel₀ hJ
  calc
    _ = ∫ x : X, J * godementSectionIntegrand d Φ f g
        (k.val * ((upperEntryCoordinates n).symm x).val * logTorus y) :=
      (integral_const_mul _ _).symm
    _ = ∫ x : X, F (scaleUpperEntries y x) := by
      apply integral_congr_ae
      filter_upwards [] with x
      let u : N := (upperEntryCoordinates n).symm x
      have h := godementSectionIntegrand_triangular d ds Φ hf g u k y
        (positiveDiagonalUnits y) (fun _ => rfl)
      have hlog : logTorus y = Iwasawa.diagonalUnits (positiveDiagonalUnits y) := rfl
      simpa only [F, J, triangularGodementKernel, u, hlog, Homeomorph.apply_symm_apply] using h
    _ = ∫ z, F z ∂(volume : Measure X).map (scaleUpperEntries y) :=
      (integral_map (continuous_scaleUpperEntries y).measurable.aemeasurable
        hcont.aestronglyMeasurable).symm
    _ = J * ∫ z : X, F z := by
      rw [map_scaleUpperEntries, integral_smul_nnreal_measure]
      simp only [NNReal.smul_def, Complex.real_smul, J]

/-- After absolute convergence, the smaller-group Godement integral is a fixed positive
multiple of the triangular-coordinate integral. -/
def ComplexGodementTriangularIntegralStatement (n : ℕ) : Prop :=
  ∀ (μ : Measure (Langlands.GeneralLinear n ℂ)) (κ : Measure (unitaryCompact ℂ n)),
    μ.IsHaarMeasure → μ.IsMulRightInvariant → κ.IsHaarMeasure →
    ∃ c : ℝ≥0, 0 < c ∧ ∀ (d : ComplexCharacterData) (ds : List ComplexCharacterData)
      (Φ : Matrix (Fin n) (Fin (n + 1)) ℂ → ℂ) (f : Langlands.GeneralLinear n ℂ → ℂ),
      Continuous Φ → f ∈ complexStandardModule n ds →
      ∀ (g : Langlands.GeneralLinear (n + 1) ℂ),
        Integrable (godementSectionIntegrand d Φ f g) μ →
        (∫ h, godementSectionIntegrand d Φ f g h ∂μ) =
          (c : ℂ) * ∫ k, (∫ y : Fin n → ℝ, ∫ z : UpperEntryPair n → ℂ,
            triangularGodementKernel d ds Φ f g k y z) ∂κ

theorem complexGodementTriangularIntegral : ComplexGodementTriangularIntegralStatement n := by
  intro μ κ hμ hright hκ
  let : μ.IsHaarMeasure := hμ
  let : μ.IsMulRightInvariant := hright
  let : κ.IsHaarMeasure := hκ
  obtain ⟨c, hc, hq⟩ := exists_rightIwasawa_entryMeasure μ κ
  refine ⟨c, hc, fun d ds Φ f hΦ hf g hI => ?_⟩
  let q : (Y × X) × K → G :=
    fun p => p.2.val * ((upperEntryCoordinates n).symm p.1.2).val * logTorus p.1.1
  let η := ((volume : Measure Y).prod (volume : Measure X)).prod κ
  let I := godementSectionIntegrand d Φ f g
  have hqM : Measurable q :=
    ((measurable_subtype_coe.comp measurable_snd).mul
      (measurable_subtype_coe.comp ((upperEntryCoordinates n).symm.measurable.comp
        (measurable_snd.comp measurable_fst)))).mul
      (ComplexLocalIwasawa.continuous_logTorus.measurable.comp (measurable_fst.comp measurable_fst))
  change μ = c • η.map q at hq
  change Integrable I μ at hI
  rw [hq] at hI
  have hi : Integrable I (η.map q) :=
    (integrable_smul_measure (ENNReal.coe_ne_zero.mpr hc.ne') ENNReal.coe_ne_top).mp hI
  have hcomp := (integrable_map_measure hi.aestronglyMeasurable hqM.aemeasurable).mp hi
  have hFubini := integral_prod_symm (I ∘ q) hcomp
  change (∫ x, I (q x) ∂η) = _ at hFubini
  rw [hq, integral_smul_nnreal_measure, integral_map hqM.aemeasurable hi.aestronglyMeasurable, hFubini]
  simp only [NNReal.smul_def, Complex.real_smul]
  congr 1
  apply integral_congr_ae
  filter_upwards [hcomp.prod_left_ae] with k hk
  rw [integral_prod _ hk]
  apply integral_congr_ae
  filter_upwards [] with y
  exact integral_triangular_entries d ds Φ hΦ hf g k y

end Langlands.Global.RankinSelbergGlobal.ComplexGodement
