import Langlands.BaseChange.LeviNormDescent
import Langlands.Representation.GodementJacquet.TwoBlockParabolicHaar

/-! The determinant change of variables for ordinary two-block orbital descent. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.GodementJacquet.TwoBlock Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet
open scoped Kronecker NNReal

universe u

section Algebra

variable {R : Type u} [Field R]
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R
local notation "Coords" => Fin (m 0 + 1) × Fin (m 1 + 1)

/-- The entrywise matrix of `x ↦ x - γ₀⁻¹ x γ₁` on the upper radical. -/
def ordinaryRadicalMatrix (γ : (B).Levi R) : Matrix Coords Coords R :=
  1 - (((γ 0)⁻¹ : GeneralLinear (m 0 + 1) R).val ⊗ₖ (γ 1).val.transpose)

theorem ordinaryRadicalMatrix_apply (γ : (B).Levi R) (x : Rect)
    [TopologicalSpace R] [IsTopologicalRing R] [MeasurableSpace R] [BorelSpace R]
    [SecondCountableTopology R] [LocallyCompactSpace R] :
    Matrix.toLin' (ordinaryRadicalMatrix h γ) (rectangularCoordinates x) =
      rectangularCoordinates (x - ((γ 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * x * (γ 1).val) := by
  rw [ordinaryRadicalMatrix, map_sub, LinearMap.sub_apply, Matrix.toLin'_one,
    LinearMap.id_apply, ← rectangularCoordinates_mul, map_sub]

theorem upperRadical_conj_leviEmbedding (γ : (B).Levi R) (x : Rect) :
    (upperRadical h R x)⁻¹ * (B).leviEmbedding R γ * upperRadical h R x =
      parabolicPoint h (γ, x - ((γ 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * x * (γ 1).val) := by
  simpa only [parabolicPoint, map_one, one_mul, inv_one, mul_assoc] using
    (parabolicPoint_inv_mul h (1 : (B).Levi R) γ x x)

private theorem ordinaryRadicalDifference_eq_zero {γ : (B).Levi R}
    (hCop : Pairwise fun i j : Fin 2 => IsCoprime (γ i).val.charpoly (γ j).val.charpoly)
    {x : Rect} (hx : x - ((γ 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * x * (γ 1).val = 0) :
    x = 0 := by
  have hFixed := sub_eq_zero.mp hx
  have hComm := upperRadical_mul_leviEmbedding h γ x
  rw [← hFixed] at hComm
  have hLevi := mem_leviSubgroup_of_commute B γ hCop (Commute.symm hComm)
  ext a b
  have hz := (mem_leviSubgroup_iff_offBlock_eq_zero B (upperRadical h R x)).mp hLevi
    0 1 a b (show (0 : Fin 2) ≠ 1 by decide)
  rw [upperRadical_index_zero_one] at hz
  exact hz

theorem ordinaryRadicalMatrix_det_conj (γ L : (B).Levi R) :
    (ordinaryRadicalMatrix h (L⁻¹ * γ * L)).det = (ordinaryRadicalMatrix h γ).det := by
  let U := ((L 0)⁻¹ : GeneralLinear (m 0 + 1) R).val ⊗ₖ (L 1).val.transpose
  let V := (L 0).val ⊗ₖ ((L 1)⁻¹ : GeneralLinear (m 1 + 1) R).val.transpose
  have hUV : U * V = 1 := by
    dsimp only [U, V]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul, ← Units.val_mul, ← Units.val_mul,
      inv_mul_cancel, inv_mul_cancel, Units.val_one, Units.val_one, Matrix.transpose_one,
      Matrix.one_kronecker_one]
  have hConj : ordinaryRadicalMatrix h (L⁻¹ * γ * L) = U * ordinaryRadicalMatrix h γ * V := by
    unfold ordinaryRadicalMatrix
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, hUV]
    dsimp only [U, V]
    rw [← Matrix.mul_kronecker_mul, ← Matrix.mul_kronecker_mul, ← Matrix.transpose_mul,
      ← Matrix.transpose_mul]
    simp only [Pi.mul_apply, Pi.inv_apply, mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
  have hD : U.det * V.det = 1 := by rw [← Matrix.det_mul, hUV, Matrix.det_one]
  rw [hConj, Matrix.det_mul, Matrix.det_mul, mul_comm U.det, mul_assoc, hD, mul_one]

end Algebra

section Haar

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

local instance ordinaryRadicalFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance ordinaryRadicalFieldValuativeRel : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance ordinaryRadicalFieldLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance ordinaryRadicalFieldT2 : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2
local instance ordinaryRadicalFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance ordinaryRadicalFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance ordinaryRadicalFieldSecondCountable : SecondCountableTopology F.Carrier :=
  F.canonicalTopologicalData.secondCountableTopology

variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier

theorem ordinaryRadicalMatrix_det_ne_zero (γ : (B).Levi F.Carrier)
    (hCop : Pairwise fun i j : Fin 2 => IsCoprime (γ i).val.charpoly (γ j).val.charpoly) :
    (ordinaryRadicalMatrix h γ).det ≠ 0 := by
  rw [← LinearMap.det_toLin', ne_eq, LinearMap.det_eq_zero_iff_ker_ne_bot, not_not]
  apply LinearMap.ker_eq_bot'.mpr
  intro y hy
  let x : Rect := rectangularCoordinates.symm y
  have he : rectangularCoordinates x = y := rectangularCoordinates.apply_symm_apply y
  rw [← he, ordinaryRadicalMatrix_apply h γ] at hy
  have hx : x - ((γ 0)⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * x * (γ 1).val = 0 :=
    rectangularCoordinates.injective (hy.trans (map_zero rectangularCoordinates).symm)
  rw [← he, ordinaryRadicalDifference_eq_zero h hCop hx, map_zero]

/-- The change of variables for conjugation by the upper radical multiplies the
radical integral by the inverse residue-normalized determinant of the difference map. -/
theorem integral_upperRadical_conj_leviEmbedding (γ : (B).Levi F.Carrier)
    (hCop : Pairwise fun i j : Fin 2 => IsCoprime (γ i).val.charpoly (γ j).val.charpoly)
    (dx : Measure Rect) [dx.IsAddHaarMeasure]
    (f : GeneralLinear (t + 1) F.Carrier → ℂ) (hf : Continuous f) :
    ∫ x, f ((upperRadical h F.Carrier x)⁻¹ * (B).leviEmbedding F.Carrier γ *
        upperRadical h F.Carrier x) ∂dx =
      (F.canonicalTopologicalData.normalizedAbsHom (ordinaryRadicalMatrix h γ).det)⁻¹ •
        ∫ x, f (parabolicPoint h (γ, x)) ∂dx := by
  let T := F.canonicalTopologicalData
  let D (x : Rect) := x - ((γ 0)⁻¹ : GeneralLinear (m 0 + 1) F.Carrier).val * x * (γ 1).val
  have hD : Continuous D :=
    continuous_id.sub ((continuous_const.matrix_mul continuous_id).matrix_mul continuous_const)
  have hCoord (x : Rect) :
      rectangularCoordinates.symm (Matrix.toLin' (ordinaryRadicalMatrix h γ) (rectangularCoordinates x)) =
        D x := by
    rw [ordinaryRadicalMatrix_apply, rectangularCoordinates.symm_apply_apply]
  have hScale (a : F.Carrier) (ha : a ≠ 0) :
      (Measure.addHaar : Measure F.Carrier).map (fun x => a * x) =
        (T.normalizedAbsHom a)⁻¹ • Measure.addHaar :=
    padicScalarHaarScaling F T Measure.addHaar (Units.mk0 a ha)
  have hMap := haarMeasure_map_in_coordinates Measure.addHaar T.normalizedAbsHom hScale
    rectangularCoordinates dx (ordinaryRadicalMatrix_det_ne_zero F h γ hCop)
  simp_rw [hCoord] at hMap
  have hCont : Continuous (fun x : Rect => f (parabolicPoint h (γ, x))) :=
    hf.comp ((continuous_parabolicPoint h F.Carrier).comp (continuous_const.prodMk continuous_id))
  simp_rw [upperRadical_conj_leviEmbedding h γ]
  change (∫ x, f (parabolicPoint h (γ, D x)) ∂dx) = _
  rw [← integral_map hD.measurable.aemeasurable hCont.aestronglyMeasurable, hMap,
    integral_smul_nnreal_measure]

end Haar

end Langlands.BaseChange
