import Langlands.Representation.RankinSelberg.RankOneMatrixUnfolding
import Langlands.AllField.Representation.GodementJacquet.Zeta
import Langlands.AllField.Representation.RankinSelberg.RankOneMatrixUnipotentIntegral
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

namespace Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg.RankOneIwasawa hiding ColBound abv_det_eq_one ae_outerMeasure_mem colBound_of_inv colBound_zero congruenceGroup congruenceGroup_le_integral conj_mem_congruenceGroup continuous_det_units continuous_point continuous_torusCoord continuous_torusModulus continuous_weight det_point det_unipotent_mul determinantWeight_diagPoint diagPoint elemUnipotent elemUnipotent_val exists_congruenceGroup_le exists_cornerSchwartz exists_lattice_nontrivial exists_lattice_subset exists_mem_lattice exists_mem_matLattice exists_ne_zero_of_unipotentTransform_ne_zero exists_schwartz_congruence glLocallyCompact glLocallyCompactU glOneMeasure glOneMeasure_sigmaFinite glSecondCountable glSecondCountableU instBorelSpaceGeneralLinearHAddNatOfNatCarrier instBorelSpaceGeneralLinearHAddNatOfNatCarrier_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instBorelSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instBorelSpaceUnitsCarrier instIsNonarchimedeanLocalFieldCarrier instIsNonarchimedeanLocalFieldCarrier_1 instIsNonarchimedeanLocalFieldCarrier_2 instIsNonarchimedeanLocalFieldCarrier_3 instIsNonarchimedeanLocalFieldCarrier_4 instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier instMeasurableSpaceGeneralLinearHAddNatOfNatCarrier_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_1 instMeasurableSpaceSubtypeGeneralLinearHAddNatOfNatCarrierMemSubgroupUpperUnipotent_2 instMeasurableSpaceUnitsCarrier instMeasurableSpaceUnitsCarrier_1 instSecondCountableTopologyCarrier instSecondCountableTopologyCarrier_1 instT2SpaceCarrier instT2SpaceCarrier_1 instTopologicalSpaceCarrier instTopologicalSpaceCarrier_1 instTopologicalSpaceCarrier_2 instTopologicalSpaceCarrier_3 instTopologicalSpaceCarrier_4 instValuativeRelCarrier instValuativeRelCarrier_1 instValuativeRelCarrier_2 instValuativeRelCarrier_3 instValuativeRelCarrier_4 integralSet integralSubgroup_mem_matLattice integral_matrixIntegrand_unfold integral_mul_matLattice inv_mem_lattice_of_notMem inv_mem_of_colBound isCompact_lattice isOpen_congruenceGroup isOpen_lattice isOpen_matLattice iwasawaMeasure iwasawaMeasure_point_preimage iwasawaMeasure_sFinite lattice_mono lattice_mul map_iwasawaMeasure_prod map_unfoldedMeasure matLattice matLattice_basis matLattice_mono matLattice_mul matLattice_mul_integral matrixIntegrand_unfoldedPoint matrixLocallyCompact matrixLocallyCompactU measurable_point measurable_unfoldedPoint measurePreserving_shift mem_lattice_zero_iff mem_matLattice mem_matLattice_of_support mul_sub_one_mem one_add_mem_lattice_zero one_add_single_apply one_mem_lattice_zero outerMeasure outerMeasure_sFinite parameterBase_isMulLeftInvariant parameterMeasure parameterMeasure_eq_prod parameterMeasure_sigmaFinite schwartzOfLattice schwartzOfLattice_apply schwartz_invariance schwartz_support_bound standardCharacter_elemUnipotent tailMeasure tailMeasure_sigmaFinite torusModulus torusModulus_apply torusModulus_cons_one torusModulus_eq_one unfoldedMeasure unfoldedMeasure_eq unfoldedPoint unfoldedPoint_eq unipotentConj_map unipotentLocallyCompact unipotentLocallyCompactU unipotentSecondCountable unipotentSecondCountableU unipotentTransform unipotentTransform_diag_bounds unipotentTransform_eq_zero_of_shift unipotentTransform_mul_right unipotent_col_zero unipotent_mul_single_zero unitsSecondCountable weight weight_apply weight_glOne weight_split
open Langlands.AllField.RankinSelberg.RankOneIwasawa
open Langlands.RankinSelberg hiding EqualRankAnalyticStatement LastRowCompactOrbitStatement QuotientHaarExistenceStatement UnequalRankAnalyticStatement UnequalRankCommonGeneratorStatement ZeroRowLastRowCutoffStatement diagonalConj_map lastRowCompactOrbit normalizedAbsoluteValue normalizedAbsoluteValue_apply singleton_modulus_real zeroRowLastRowCutoff
open Langlands.AllField.RankinSelberg

open Langlands.GeneralLinear
open Langlands.HarmonicAnalysis hiding padicLatticeGeometry padicRectangularHaarScaling padicScalarHaarScaling
open Langlands.AllField.HarmonicAnalysis
open Langlands.Whittaker
open Langlands.Conductor

universe uF

section Unfolding

variable (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F]

local instance : T2Space F := (⟨⟩ : LocalFieldData F).fieldT2
local instance : SecondCountableTopology F :=
  (⟨⟩ : LocalFieldData F).secondCountableTopology
local instance (m : ℕ) : MeasurableSpace (Langlands.GeneralLinear (m + 1) F) := borel _
local instance (m : ℕ) : BorelSpace (Langlands.GeneralLinear (m + 1) F) := ⟨rfl⟩
local instance (m : ℕ) : MeasurableSpace (upperUnipotent (m + 1) F) := borel _
local instance (m : ℕ) : BorelSpace (upperUnipotent (m + 1) F) := ⟨rfl⟩
local instance : MeasurableSpace Fˣ := borel _

local instance glSecondCountableU (m : ℕ) :
    SecondCountableTopology (Langlands.GeneralLinear m F) := by
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F) :=
    inferInstanceAs (SecondCountableTopology (Fin m → Fin m → F))
  have : SecondCountableTopology (Matrix (Fin m) (Fin m) F)ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  exact Units.isInducing_embedProduct.secondCountableTopology

local instance unipotentSecondCountableU (m : ℕ) :
    SecondCountableTopology (upperUnipotent m F) :=
  TopologicalSpace.Subtype.secondCountableTopology
    (upperUnipotent m F : Set (Langlands.GeneralLinear m F))

local instance matrixLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (Matrix (Fin m) (Fin m) F) :=
  inferInstanceAs (LocallyCompactSpace (Fin m → Fin m → F))

local instance glLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (Langlands.GeneralLinear m F) :=
  inferInstance

local instance unipotentLocallyCompactU (m : ℕ) :
    LocallyCompactSpace (upperUnipotent m F) :=
  UpperUnipotent.locallyCompactSpace

local notation "abv" => normalizedAbsoluteValue (⟨⟩ : LocalFieldData F)

/-- The integral subgroup `GL_(n+1)(O)` as a set. -/
abbrev integralSet (n : ℕ) : Set (Langlands.GeneralLinear (n + 1) F) :=
  (integralSubgroup (ValuativeRel.valuation F).integer n :
    Set (Langlands.GeneralLinear (n + 1) F))

variable (ψ : UnitaryAdditiveCharacter F) {n : ℕ}

/-- The point `D(g, a) k = diag(det g / ∏ a, a) · k`. -/
def diagPoint (x : Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
    Langlands.GeneralLinear (n + 1) F)) : Langlands.GeneralLinear (n + 1) F :=
  Iwasawa.diagonalUnits (torusCoord n (x.1, x.2.1)) * x.2.2

/-- The product measure `|det g|⁻ⁿ dg × ω(1, a) da × dk|_K` of the outer variables. -/
def outerMeasure (n : ℕ) : Measure (Langlands.GeneralLinear (0 + 1) F ×
    ((Fin n → Fˣ) × Langlands.GeneralLinear (n + 1) F)) :=
  (glOneMeasure F n).prod ((tailMeasure F n).prod
    ((generalLinearHaar F n).restrict (integralSet F n)))

instance outerMeasure_sFinite (n : ℕ) : SFinite (outerMeasure F n) := by
  unfold outerMeasure
  infer_instance

theorem unfoldedMeasure_eq (n : ℕ) :
    unfoldedMeasure F n = (outerMeasure F n).prod (unipotentHaar F n) := rfl

theorem unfoldedPoint_eq (x : Langlands.GeneralLinear (0 + 1) F ×
    ((Fin n → Fˣ) × Langlands.GeneralLinear (n + 1) F))
    (u : upperUnipotent (n + 1) F) :
    unfoldedPoint F (x, u) = (u : Langlands.GeneralLinear (n + 1) F) * diagPoint F x := by
  simp only [unfoldedPoint, point, diagPoint, mul_assoc]

theorem det_unipotent_mul (u : upperUnipotent (n + 1) F)
    (y : Langlands.GeneralLinear (n + 1) F) :
    Matrix.det ((u : Langlands.GeneralLinear (n + 1) F).val * y.val) =
      Matrix.det y.val := by
  rw [Matrix.det_mul, Matrix.det_of_isUpperTriangular u.property.1,
    Finset.prod_eq_one fun i _ => UpperUnipotent.entry_diag u i, one_mul]

/-- The absolute value of the determinant of an integral matrix is one. -/
theorem abv_det_eq_one {k : Langlands.GeneralLinear (n + 1) F} (hk : k ∈ integralSet F n) :
    abv (Matrix.det k.val) = 1 := by
  obtain ⟨h1, h2⟩ := integralSubgroup_mem_matLattice F hk
  have hint : ∀ {A : Matrix (Fin (n + 1)) (Fin (n + 1)) F},
      A ∈ matLattice F (n + 1) 0 → abv (Matrix.det A) ≤ 1 := by
    intro A hA
    rw [normalizedAbsoluteValue_apply,
      (⟨⟩ : LocalFieldData F).normalizedAbs_le_one_iff_mem_integers]
    rw [Matrix.det_apply]
    refine Subring.sum_mem _ fun σ _ => ?_
    refine Subring.zsmul_mem _ (Subring.prod_mem _ fun i _ => ?_) _
    exact (mem_lattice_zero_iff F _).1 (hA _ _)
  have hmul : abv (Matrix.det k.val) * abv (Matrix.det (k⁻¹).val) = 1 := by
    rw [← map_mul, ← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.det_one, map_one]
  have ha := hint h1
  have hb := hint h2
  have ha0 := AbsoluteValue.nonneg (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (Matrix.det k.val)
  have hb0 := AbsoluteValue.nonneg (normalizedAbsoluteValue (⟨⟩ : LocalFieldData F))
    (Matrix.det (k⁻¹).val)
  nlinarith

theorem determinantWeight_diagPoint (s : ℂ)
    (x : Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F)) (hk : x.2.2 ∈ integralSet F n) :
    determinantWeight abv (diagPoint F x) s = determinantWeight abv x.1 s := by
  unfold determinantWeight
  have hd := det_point F ((x.1, x.2.1), (1 : upperUnipotent (n + 1) F))
  simp only [point, OneMemClass.coe_one, one_mul] at hd
  rw [diagPoint, Units.val_mul, Matrix.det_mul, map_mul, abv_det_eq_one F hk, mul_one,
    ← Matrix.GeneralLinearGroup.val_det_apply, hd, Matrix.GeneralLinearGroup.val_det_apply]

/-- Almost every outer parameter has integral `k`. -/
theorem ae_outerMeasure_mem :
    ∀ᵐ x ∂(outerMeasure F n), x.2.2 ∈ integralSet F n := by
  have hK : MeasurableSet (integralSet F n) := by
    unfold integralSet
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F n 0).isOpen.measurableSet
  rw [ae_iff]
  have : {x : Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F) | ¬ x.2.2 ∈ integralSet F n} =
      Set.univ ×ˢ (Set.univ ×ˢ (integralSet F n)ᶜ) := by
    ext x
    simp
  rw [this, outerMeasure, Measure.prod_prod, Measure.prod_prod, Measure.restrict_apply hK.compl,
    Set.compl_inter_self, measure_empty, mul_zero, mul_zero]

/-- The matrix integrand at an unfolded point, using left equivariance of `f`. -/
theorem matrixIntegrand_unfoldedPoint
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hf : ∀ (u : upperUnipotent (n + 1) F) y,
      f ((u : Langlands.GeneralLinear (n + 1) F) * y) = (standardCharacter ψ n u : ℂ) * f y)
    (s : ℂ) (x : Langlands.GeneralLinear (0 + 1) F × ((Fin n → Fˣ) ×
      Langlands.GeneralLinear (n + 1) F)) (u : upperUnipotent (n + 1) F) :
    GodementJacquet.matrixIntegrand abv Φ s f (unfoldedPoint F (x, u)) =
      Φ ((u : Langlands.GeneralLinear (n + 1) F).val * (diagPoint F x).val) *
        (standardCharacter ψ n u : ℂ) *
          (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s) := by
  rw [unfoldedPoint_eq, GodementJacquet.matrixIntegrand, hf]
  have hw : determinantWeight abv ((u : Langlands.GeneralLinear (n + 1) F) *
      diagPoint F x) s = determinantWeight abv (diagPoint F x) s := by
    unfold determinantWeight
    rw [Units.val_mul, det_unipotent_mul]
  rw [hw, Units.val_mul]
  ring

/-- **Unfolding, integral form.** If the matrix integral converges absolutely, the
unipotent variable can be integrated first. -/
theorem integral_matrixIntegrand_unfold
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F))
    (f : Langlands.GeneralLinear (n + 1) F → ℂ)
    (hf : ∀ (u : upperUnipotent (n + 1) F) y,
      f ((u : Langlands.GeneralLinear (n + 1) F) * y) = (standardCharacter ψ n u : ℂ) * f y)
    (s : ℂ)
    (hint : Integrable (GodementJacquet.matrixIntegrand abv Φ s f) (generalLinearHaar F n)) :
    Integrable (fun x => unipotentTransform F ψ Φ (diagPoint F x).val *
        (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s)) (outerMeasure F n) ∧
      ∫ y, GodementJacquet.matrixIntegrand abv Φ s f y ∂(generalLinearHaar F n) =
        ∫ x, unipotentTransform F ψ Φ (diagPoint F x).val *
          (f (diagPoint F x) * determinantWeight abv (diagPoint F x) s) ∂(outerMeasure F n) := by
  have hπ : AEMeasurable (unfoldedPoint F (n := n)) (unfoldedMeasure F n) :=
    (measurable_unfoldedPoint F n).aemeasurable
  rw [← map_unfoldedMeasure F n] at hint
  have hint' := (integrable_map_measure hint.aestronglyMeasurable hπ).1 hint
  rw [unfoldedMeasure_eq] at hint'
  have hinner : ∀ x, ∫ u, (GodementJacquet.matrixIntegrand abv Φ s f ∘ unfoldedPoint F)
      (x, u) ∂(unipotentHaar F n) = unipotentTransform F ψ Φ (diagPoint F x).val *
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

end Unfolding

end Langlands.AllField.RankinSelberg.RankOneIwasawa
