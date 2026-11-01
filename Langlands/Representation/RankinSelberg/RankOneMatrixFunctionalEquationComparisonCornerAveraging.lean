import Langlands.Representation.RankinSelberg.RankOneMatrixFunctionalEquationComparisonCornerFourier
import Langlands.Representation.RankinSelberg.RankOneMatrixWhittakerComparisonExpansion

/-! Actual compact parameter kernels for normalized-determinant corner averaging. -/

noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace Langlands.RankinSelberg.RankOneIwasawa

open MeasureTheory Topology GeneralLinear HarmonicAnalysis Conductor

universe uF

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance cornerAvgTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance cornerAvgValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance cornerAvgLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance cornerAvgT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance cornerAvgTotallyDisconnected : TotallyDisconnectedSpace F.Carrier := by
  let : NonarchimedeanRing F.Carrier := by
    convert! ValuativeRel.nonarchimedeanRing F.Carrier
    exact Valuation.toTopologicalSpace_eq _
  infer_instance
local instance cornerAvgMeasurable : MeasurableSpace F.Carrier := borel _
local instance cornerAvgBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance cornerAvgNMeasurable (n : ℕ) :
    MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance cornerAvgNBorel (n : ℕ) :
    BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩

local notation "𝓛" => F.canonicalTopologicalData.additiveLattice

/-- The determinant-normalized diagonal/integral parameter point. -/
def cornerAveragingPoint {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    Langlands.GeneralLinear (n + 1) F.Carrier := diagPoint F (1, y)

theorem continuous_cornerAveragingPoint (n : ℕ) :
    Continuous (cornerAveragingPoint F (n := n)) :=
  (continuous_diagPoint F).comp (continuous_const.prodMk continuous_id)

/-- Its determinant is exactly the determinant of the integral parameter. -/
theorem det_cornerAveragingPoint {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    Matrix.GeneralLinearGroup.det (cornerAveragingPoint F y) =
      Matrix.GeneralLinearGroup.det y.2 := by
  simp only [cornerAveragingPoint, diagPoint, map_mul, det_diagonalUnits,
    Fin.prod_univ_succ, torusCoord_zero, torusCoord_succ, map_one, one_mul,
    inv_mul_cancel, one_mul]

theorem abv_det_cornerAveragingPoint {n : ℕ}
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier)
    (hy : y.2 ∈ integralSet F n) :
    normalizedAbsoluteValue F.canonicalTopologicalData
      (Matrix.det (cornerAveragingPoint F y).val) = 1 := by
  have he := congrArg (fun x : F.Carrierˣ => (x : F.Carrier)) (det_cornerAveragingPoint F y)
  simp only [Matrix.GeneralLinearGroup.val_det_apply] at he
  rw [he]
  exact abv_det_eq_one F hy

/-- The scalar corner at the determinant of `g` is the actual Iwasawa point. -/
theorem cornerFamily_cornerAveragingPoint
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
    (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :
    cornerFamily F ψ n Φ (cornerAveragingPoint F y)
        ((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) =
      unipotentTransform F ψ Φ (diagPoint F (g, y)).val := by
  unfold cornerFamily cornerAveragingPoint diagPoint
  simp only [Units.val_mul, Iwasawa.diagonalUnits_val, ← Matrix.mul_assoc,
    Matrix.diagonal_mul_diagonal]
  congr 2
  apply congrArg Matrix.diagonal
  funext i
  induction i using Fin.cases with
  | zero => simp [torusCoord_zero]
  | succ i => simp [torusCoord_succ]

/-- Compact clopen tail bounds together with the actual integral subgroup. -/
def cornerParameterBox (n : ℕ) (R E : ℤ) :
    Set ((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) :=
  (Set.univ.pi fun _ => {x : F.Carrierˣ | (x : F.Carrier) ∈ 𝓛 R ∧
    ((x⁻¹ : F.Carrierˣ) : F.Carrier) ∈ 𝓛 E}) ×ˢ integralSet F n

theorem isCompact_cornerParameterBox (n : ℕ) (R E : ℤ) :
    IsCompact (cornerParameterBox F n R E) :=
  (isCompact_univ_pi fun _ => isCompact_unitBox F R E).prod (isCompact_integralSet F n)

theorem isClopen_cornerParameterBox (n : ℕ) (R E : ℤ) :
    IsClopen (cornerParameterBox F n R E) := by
  refine ⟨(isCompact_cornerParameterBox F n R E).isClosed, ?_⟩
  have hU : IsOpen {x : F.Carrierˣ | (x : F.Carrier) ∈ 𝓛 R ∧
      ((x⁻¹ : F.Carrierˣ) : F.Carrier) ∈ 𝓛 E} :=
    ((isOpen_lattice F R).preimage Units.continuous_val).inter
      ((isOpen_lattice F E).preimage Units.continuous_coe_inv)
  have hK : IsOpen (integralSet F n) := by
    unfold integralSet
    rw [← levelSubgroup_zero]
    exact (levelOpenSubgroup F.Carrier n 0).isOpen
  exact (isOpen_set_pi Set.finite_univ (fun _ _ => hU)).prod hK

/-- Actual diagonal bounds are uniform in the determinant coordinate. -/
theorem exists_cornerParameterBox_support
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier)) :
    ∃ R E : ℤ, ∀ (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
      (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier),
      y.2 ∈ integralSet F n →
      unipotentTransform F ψ Φ (diagPoint F (g, y)).val ≠ 0 →
        y ∈ cornerParameterBox F n R E := by
  obtain ⟨R, E, hRE⟩ := unipotentTransform_diag_bounds F ψ Φ
  refine ⟨R, E, fun g y hy hJ => ?_⟩
  have hval : (diagPoint F (g, y)).val = Matrix.diagonal (fun j =>
      (torusCoord n (g, y.1) j : F.Carrier)) * y.2.val := by
    rw [diagPoint, Units.val_mul, Iwasawa.diagonalUnits_val]
  rw [hval] at hJ
  obtain ⟨h1, h2⟩ := hRE _ y.2 hy hJ
  refine ⟨fun i _ => ⟨?_, ?_⟩, hy⟩
  · simpa using h1 i.succ
  · have := h2 i
    rwa [torusCoord_succ, ← Units.val_inv_eq_inv_val] at this

/-- A single jointly compact Schwartz kernel reconstructs every actual corner
at an integral Iwasawa parameter, with the supplied scalar measure unchanged. -/
theorem exists_cornerAveragingKernel
    (ψ : UnitaryAdditiveCharacter F.Carrier) {n : ℕ}
    (Φ : SchwartzBruhat (Matrix (Fin (n + 1)) (Fin (n + 1)) F.Carrier))
    (ν : AdditiveHaarMeasure F.Carrier) (hsd : IsSelfDual ψ ν) :
    ∃ R E : ℤ, ∃ K : SchwartzBruhat
        (((Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier) × F.Carrier),
      (∀ y v, K (y, v) = (cornerParameterBox F n R E).indicator
        (fun y => cornerCoFourierTest F ψ n Φ ν hsd (cornerAveragingPoint F y) v) y) ∧
      ∀ (g : Langlands.GeneralLinear (0 + 1) F.Carrier)
        (y : (Fin n → F.Carrierˣ) × Langlands.GeneralLinear (n + 1) F.Carrier),
        y.2 ∈ integralSet F n →
        (∫ v, ψ.complex (((Matrix.GeneralLinearGroup.det g : F.Carrierˣ) : F.Carrier) * v) *
          K (y, v) ∂ν.measure) = unipotentTransform F ψ Φ (diagPoint F (g, y)).val := by
  classical
  obtain ⟨R, E, hRE⟩ := exists_cornerParameterBox_support F ψ Φ
  obtain ⟨K, hK⟩ := exists_compact_cornerCoFourier_kernel F ψ n Φ ν hsd
    (cornerAveragingPoint F) (continuous_cornerAveragingPoint F n)
    (isCompact_cornerParameterBox F n R E) (isClopen_cornerParameterBox F n R E)
  refine ⟨R, E, K, hK, fun g y hy => ?_⟩
  by_cases hC : y ∈ cornerParameterBox F n R E
  · have he : ∀ v, K (y, v) = cornerCoFourierTest F ψ n Φ ν hsd
        (cornerAveragingPoint F y) v := fun v => by rw [hK, Set.indicator_of_mem hC]
    simp_rw [he]
    rw [integral_cornerCoFourierTest, cornerFamily_cornerAveragingPoint]
  · have he : ∀ v, K (y, v) = 0 := fun v => by rw [hK, Set.indicator_of_notMem hC]
    have hJ : unipotentTransform F ψ Φ (diagPoint F (g, y)).val = 0 := by
      by_contra hne
      exact hC (hRE g y hy hne)
    simp only [he, mul_zero, integral_zero, hJ]

end Langlands.RankinSelberg.RankOneIwasawa
