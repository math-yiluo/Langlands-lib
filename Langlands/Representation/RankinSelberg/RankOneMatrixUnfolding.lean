import Langlands.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
import Langlands.Representation.GodementJacquet.Zeta
import Langlands.LocalField.Normalization.Continuity

/-!
# Unfolding the matrix integral over the unipotent variable

For a matrix test function `Φ` and a left `(N, θ)`-equivariant function `f` on
`GL_(n+1)`, the matrix integral `∫ Φ(y) f(y) |det y|^s dy` equals the integral over
`(g, (a, k))` of `J(D(g, a) k) f(D(g, a) k) |det|^s` against
`|det g|⁻ⁿ dg × ω(1, a) da × dk|_K`, where `J` is the unipotent transform of `Φ`.
The absolute version holds for every measurable `f`.
-/

noncomputable section

open MeasureTheory Topology
open scoped NNReal ENNReal

namespace Langlands.RankinSelberg.RankOneIwasawa

open GeneralLinear HarmonicAnalysis Whittaker Conductor

universe uF

section Unfolding

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology
local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) F.Carrier) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F.Carrier) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F.Carrier) := ⟨rfl⟩
local instance : MeasurableSpace F.Carrierˣ := borel _
local instance : BorelSpace F.Carrierˣ := ⟨rfl⟩

local instance glSecondCountableU (m : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear m F.Carrier) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F.Carrier))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F.Carrier)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unipotentSecondCountableU (m : ℕ) :
    SecondCountableTopology (upperUnipotent m F.Carrier) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m F.Carrier : Set (Langlands.GeneralLinear m F.Carrier))

local instance unitsSecondCountableU : SecondCountableTopology F.Carrierˣ :=
  Units.isEmbedding_val₀.secondCountableTopology

local instance matrixLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F.Carrier) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F.Carrier))

local instance glLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear m F.Carrier) :=
  inferInstance

local instance unipotentLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m F.Carrier) :=
  UpperUnipotent.locallyCompactSpace

local instance unitsLocallyCompactU : LocallyCompactSpace F.Carrierˣ :=
  (IsOpenUnits.isOpenEmbedding_unitsVal (M := F.Carrier)).locallyCompactSpace

local notation "abv" => normalizedAbsoluteValue F.canonicalTopologicalData

/-- The integral subgroup `GL_(n+1)(O)` as a set. -/
abbrev integralSet (n : ℕ) : Set (Langlands.GeneralLinear (n + 1) F.Carrier) :=
  (integralSubgroup (ValuativeRel.valuation F.Carrier).integer n :
    Set (Langlands.GeneralLinear (n + 1) F.Carrier))

variable (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}

/-- The point `D(g, a) k = diag(det g / ∏ a, a) · k`. -/
def diagPoint (x : Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
    Langlands.GeneralLinear (n + 1) F.Carrier)) : Langlands.GeneralLinear (n + 1) F.Carrier :=
  Iwasawa.diagonalUnits (torusCoord n (x.1, x.2.1)) * x.2.2

/-- The product measure `|det g|⁻ⁿ dg × ω(1, a) da × dk|_K` of the outer variables. -/
def outerMeasure (n : ℕ) : Measure (Langlands.GeneralLinear (0 + 1) F.Carrier ×
    ((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier)) :=
  (glOneMeasure F n).prod ((tailMeasure F n).prod
    ((generalLinearHaar F.Carrier n).restrict (integralSet F n)))

instance outerMeasure_sFinite (n : ℕ) : SFinite (outerMeasure F n) := by
  unfold outerMeasure
  infer_instance

theorem unfoldedMeasure_eq (n : ℕ) :
    unfoldedMeasure F n = (outerMeasure F n).prod (unipotentHaar F.Carrier n) := rfl

theorem unfoldedPoint_eq (x : Langlands.GeneralLinear (0 + 1) F.Carrier ×
    ((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier))
    (u : upperUnipotent (n + 1) F.Carrier) :
    unfoldedPoint F (x, u) = (u : Langlands.GeneralLinear (n + 1) F.Carrier) * diagPoint F x := by
  simp only [unfoldedPoint, point, diagPoint, mul_assoc]

theorem continuous_diagPoint : Continuous (diagPoint F (n := n)) :=
  (continuous_diagonalUnits'.comp ((continuous_torusCoord F n).comp
    (continuous_fst.prodMk continuous_snd.fst))).mul continuous_snd.snd

theorem det_unipotent_mul (u : upperUnipotent (n + 1) F.Carrier)
    (y : Langlands.GeneralLinear (n + 1) F.Carrier) :
    Matrix.det ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * y.val) =
      Matrix.det y.val := by
  rw [Matrix.det_mul, Matrix.det_of_isUpperTriangular u.property.1,
    Finset.prod_eq_one fun i _ => UpperUnipotent.entry_diag u i, one_mul]

theorem measurable_determinantWeight (s : ℂ) :
    Measurable fun y : Langlands.GeneralLinear (n + 1) F.Carrier => determinantWeight abv y s := by
  have hc : Continuous fun y : Langlands.GeneralLinear (n + 1) F.Carrier =>
      ((abv (Matrix.det y.val) : ℝ) : ℂ) := by
    have h := F.canonicalTopologicalData.continuous_normalizedAbs
    exact Complex.continuous_ofReal.comp (h.comp Units.continuous_val.matrix_det)
  exact hc.measurable.pow_const s

/-- The absolute value of the determinant of an integral matrix is one. -/
theorem abv_det_eq_one {k : Langlands.GeneralLinear (n + 1) F.Carrier} (hk : k ∈ integralSet F n) :
    abv (Matrix.det k.val) = 1 := by
  obtain ⟨h1, h2⟩ := integralSubgroup_mem_matLattice F hk
  have hint : ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier},
      A ∈ matLattice F (n + 1) 0 → abv (Matrix.det A) ≤ 1 := by
    intro A hA
    rw [normalizedAbsoluteValue_apply,
      F.canonicalTopologicalData.normalizedAbs_le_one_iff_mem_integers]
    rw [Matrix.det_apply]
    refine Subring.sum_mem _ fun σ _ => ?_
    refine Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => ?_) _
    exact (mem_lattice_zero_iff F _).1 (hA _ _)
  have hmul : abv (Matrix.det k.val) * abv (Matrix.det (k⁻¹).val) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, map_one]
  have ha := hint h1
  have hb := hint h2
  have ha0 := AbsoluteValue.nonneg (normalizedAbsoluteValue F.canonicalTopologicalData)
    (Matrix.det k.val)
  have hb0 := AbsoluteValue.nonneg (normalizedAbsoluteValue F.canonicalTopologicalData)
    (Matrix.det (k⁻¹).val)
  nlinarith

theorem determinantWeight_diagPoint (s : ℂ)
    (x : Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier)) (hk : x.2.2 ∈ integralSet F n) :
    determinantWeight abv (diagPoint F x) s = determinantWeight abv x.1 s := by
  unfold determinantWeight
  have hd := det_point F ((x.1, x.2.1), (1 : upperUnipotent (n + 1) F.Carrier))
  simp only [point, OneMemClass.coe_one, one_mul] at hd
  rw [diagPoint, Units.val_mul, Matrix.det_mul, map_mul, abv_det_eq_one F hk, mul_one,
    ← Matrix.GeneralLinearGroup.val_det_apply, hd, Matrix.GeneralLinearGroup.val_det_apply]

/-- Almost every outer parameter has integral `k`. -/
theorem ae_outerMeasure_mem :
    ∀ᵐ x ∂(outerMeasure F n), x.2.2 ∈ integralSet F n := by
  have hK : MeasurableSet (integralSet F n) := by
    unfold integralSet
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F.Carrier n 0).isOpen.measurableSet
  rw [ae_iff]
  have : {x : Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier) | ¬ x.2.2 ∈ integralSet F n} =
      Set.univ ×ˢ (Set.univ ×ˢ (integralSet F n)ᶜ) := by
    ext x
    simp
  rw [this, outerMeasure, Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hK.compl,
    Set.compl_inter_self, measure_empty, mul_zero, mul_zero]

/-- The matrix integrand at an unfolded point, using left equivariance of `f`. -/
theorem matrixIntegrand_unfoldedPoint
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ (u : upperUnipotent (n + 1) F.Carrier) y,
      f ((u : Langlands.GeneralLinear (n + 1) F.Carrier) * y) = (standardCharacter ψ n u : ℂ) * f y)
    (s : ℂ) (x : Langlands.GeneralLinear (0 + 1) F.Carrier × ((Fin n → F.Carrierˣ) ×
      Langlands.GeneralLinear (n + 1) F.Carrier)) (u : upperUnipotent (n + 1) F.Carrier) :
    GodementJacquet.matrixIntegrand abv Φ s f (unfoldedPoint F (x, u)) =
      Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val * (diagPoint F x).val) *
        (standardCharacter ψ n u : ℂ) *
          (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s) := by
  rw [unfoldedPoint_eq, GodementJacquet.matrixIntegrand, hf]
  have hw : determinantWeight abv ((u : Langlands.GeneralLinear (n + 1) F.Carrier) *
      diagPoint F x) s = determinantWeight abv (diagPoint F x) s := by
    unfold determinantWeight
    rw [Units.val_mul, det_unipotent_mul]
  rw [hw, Units.val_mul]
  ring

/-- **Unfolding, integral form.** If the matrix integral converges absolutely, the
unipotent variable can be integrated first. -/
theorem integral_matrixIntegrand_unfold
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ)
    (hf : ∀ (u : upperUnipotent (n + 1) F.Carrier) y,
      f ((u : Langlands.GeneralLinear (n + 1) F.Carrier) * y) = (standardCharacter ψ n u : ℂ) * f y)
    (s : ℂ)
    (hint : Integrable (GodementJacquet.matrixIntegrand abv Φ s f) (generalLinearHaar F.Carrier n)) :
    Integrable (fun x => unipotentTransform F ψ Φ (diagPoint F x).val *
        (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s)) (outerMeasure F n) ∧
      ∫ y, GodementJacquet.matrixIntegrand abv Φ s f y ∂(generalLinearHaar F.Carrier n) =
        ∫ x, unipotentTransform F ψ Φ (diagPoint F x).val *
          (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s) ∂(outerMeasure F n) := by
  have hπ : AEMeasurable (unfoldedPoint F (n := n)) (unfoldedMeasure F n) :=
    (measurable_unfoldedPoint F n).aemeasurable
  rw [← map_unfoldedMeasure F n] at hint
  have hint' := (integrable_map_measure hint.aestronglyMeasurable hπ).1 hint
  rw [unfoldedMeasure_eq] at hint'
  have hinner : ∀ x, ∫ u, (GodementJacquet.matrixIntegrand abv Φ s f ∘ unfoldedPoint F)
      (x, u) ∂(unipotentHaar F.Carrier n) = unipotentTransform F ψ Φ (diagPoint F x).val *
        (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s) := by
    intro x
    simp only [Function.comp_apply, matrixIntegrand_unfoldedPoint F ψ Φ f hf s x]
    rw [integral_mul_const]
    rfl
  refine ⟨?_, ?_⟩
  · have := hint'.integral_prod_left
    simp only [hinner] at this
    exact this
  · rw [← map_unfoldedMeasure F n, integral_map hπ hint.aestronglyMeasurable,
      unfoldedMeasure_eq, integral_prod (fun z => GodementJacquet.matrixIntegrand abv Φ s f
        (unfoldedPoint F z)) hint']
    exact integral_congr_ae (Filter.Eventually.of_forall hinner)

/-- **Unfolding, absolute form.** For every measurable `f`, the integral of the absolute
value of the matrix integrand is the iterated integral with the unipotent variable
innermost. -/
theorem lintegral_matrixIntegrand_unfold
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (f : Langlands.GeneralLinear (n + 1) F.Carrier → ℂ) (hfm : Measurable f)
    (hf : ∀ (u : upperUnipotent (n + 1) F.Carrier) y,
      f ((u : Langlands.GeneralLinear (n + 1) F.Carrier) * y) = (standardCharacter ψ n u : ℂ) * f y)
    (s : ℂ) :
    ∫⁻ y, ‖GodementJacquet.matrixIntegrand abv Φ s f y‖ₑ ∂(generalLinearHaar F.Carrier n) =
      ∫⁻ x, (∫⁻ u, ‖Φ ((u : Langlands.GeneralLinear (n + 1) F.Carrier).val *
          (diagPoint F x).val)‖ₑ ∂(unipotentHaar F.Carrier n)) *
        ‖f (diagPoint F x) * determinantWeight abv (diagPoint F x) s‖ₑ ∂(outerMeasure F n) := by
  have hΦ : Continuous fun y : Langlands.GeneralLinear (n + 1) F.Carrier => Φ y.val :=
    Φ.continuous.comp Units.continuous_val
  have hm : Measurable fun y : Langlands.GeneralLinear (n + 1) F.Carrier =>
      ‖GodementJacquet.matrixIntegrand abv Φ s f y‖ₑ :=
    ((hΦ.measurable.mul hfm).mul (measurable_determinantWeight F s)).enorm
  rw [← map_unfoldedMeasure F n, lintegral_map hm (measurable_unfoldedPoint F n),
    unfoldedMeasure_eq, lintegral_prod (fun z => ‖GodementJacquet.matrixIntegrand abv Φ s f
      (unfoldedPoint F z)‖ₑ) (hm.comp (measurable_unfoldedPoint F n)).aemeasurable]
  refine lintegral_congr fun x => ?_
  simp only [matrixIntegrand_unfoldedPoint F ψ Φ f hf s x, enorm_mul]
  have hθ : ∀ u : upperUnipotent (n + 1) F.Carrier, ‖(standardCharacter ψ n u : ℂ)‖ₑ = 1 := by
    intro u
    rw [← ofReal_norm, norm_standardCharacter, ENNReal.ofReal_one]
  simp only [hθ, mul_one]
  rw [lintegral_mul_const]
  exact (Φ.continuous.comp ((Units.continuous_val.comp continuous_subtype_val).mul
    continuous_const)).measurable.enorm

end Unfolding

end Langlands.RankinSelberg.RankOneIwasawa
