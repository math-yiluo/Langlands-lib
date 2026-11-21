import Langlands.BaseChange.ExactNormLeviModulus
import Langlands.BaseChange.TwoBlockLeviQuotient
import Langlands.Weil.Local.ExtensionResidue

/-! Twisted two-block radical coordinates and their Haar covariance. -/

noncomputable section

namespace Langlands.BaseChange

open MeasureTheory Langlands.GeneralLinear Langlands.HarmonicAnalysis
open Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet
open Langlands.GodementJacquet.TwoBlock Langlands.Unramified
open scoped NNReal

universe u v

section Algebra

variable {K : Type u} [Field K] {R : Type v} [Field R] [Algebra K R]
  (σ : R ≃ₐ[K] R) {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B R
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) R

private def radicalLeviAction (U : M) (x : Rect) : Rect :=
  (U 0).val * x * ((U 1)⁻¹ : GeneralLinear (m 1 + 1) R).val

private theorem radicalLeviAction_one (x : Rect) : radicalLeviAction h (1 : M) x = x := by
  simp [radicalLeviAction]

private theorem radicalLeviAction_mul (U V : M) (x : Rect) :
    radicalLeviAction h (U * V) x = radicalLeviAction h U (radicalLeviAction h V x) := by
  simp only [radicalLeviAction, Pi.mul_apply, Units.val_mul, mul_inv_rev, Matrix.mul_assoc]

private theorem radicalLeviAction_sub (U : M) (x y : Rect) :
    radicalLeviAction h U (x - y) = radicalLeviAction h U x - radicalLeviAction h U y := by
  simp only [radicalLeviAction, Matrix.mul_sub, Matrix.sub_mul]

private theorem map_radicalLeviAction (U : M) (x : Rect) :
    (radicalLeviAction h U x).map σ =
      radicalLeviAction h (leviAut σ B U) (x.map σ) := by
  change (radicalLeviAction h U x).map (σ : R →+* R) = _
  simp only [radicalLeviAction, Matrix.map_mul, leviAut_apply, ← map_inv]
  rfl

/-- The radical difference map that occurs in twisted two-block conjugation. -/
def twistedRadicalDifference (D : M) (x : Rect) : Rect :=
  x.map σ - radicalLeviAction h D⁻¹ x

theorem twistedRadicalDifference_apply (D : M) (x : Rect) :
    twistedRadicalDifference σ h D x =
      x.map σ - ((D 0)⁻¹ : GeneralLinear (m 0 + 1) R).val * x * (D 1).val := by
  simp only [twistedRadicalDifference, radicalLeviAction, Pi.inv_apply, inv_inv]

private theorem entrywiseAut_upperRadical (x : Rect) :
    entrywiseAut σ (t + 1) (upperRadical h R x) = upperRadical h R (x.map σ) := by
  apply Units.ext
  change (upperRadical h R x).val.map (σ : R →+* R) = _
  rw [upperRadical_val, upperRadical_val, Matrix.reindex_apply, Matrix.reindex_apply,
    ← Matrix.submatrix_map, Matrix.fromBlocks_map]
  simp only [Matrix.map_one (σ : R →+* R) (map_zero σ) (map_one σ),
    Matrix.map_zero (σ : R →+* R) (map_zero σ)]
  rfl

/-- The exact parabolic coordinate formula for twisted conjugation. -/
theorem twistedConj_parabolicPoint (D U : M) (x : Rect) :
    (parabolicPoint h (U, x))⁻¹ * (B).leviEmbedding R D * entrywiseAut σ (t + 1) (parabolicPoint h (U, x)) =
      parabolicPoint h (U⁻¹ * D * leviAut σ B U,
        twistedRadicalDifference σ h (U⁻¹ * D * leviAut σ B U) x) := by
  have hAut : entrywiseAut σ (t + 1) (parabolicPoint h (U, x)) =
      parabolicPoint h (leviAut σ B U, x.map σ) := by
    rw [parabolicPoint, map_mul, entrywiseAut_leviEmbedding, entrywiseAut_upperRadical]
    rfl
  rw [hAut, mul_assoc, ← parabolicPoint_left_levi, parabolicPoint_inv_mul,
    twistedRadicalDifference_apply, ← mul_assoc]

private theorem twistedRadicalDifference_twistedConj (D U : M) :
    twistedRadicalDifference σ h (U⁻¹ * D * leviAut σ B U) =
      radicalLeviAction h (leviAut σ B U)⁻¹ ∘ twistedRadicalDifference σ h D ∘ radicalLeviAction h U := by
  funext x
  simp only [Function.comp_apply, twistedRadicalDifference, map_radicalLeviAction,
    radicalLeviAction_sub, ← radicalLeviAction_mul, inv_mul_cancel, radicalLeviAction_one,
    mul_inv_rev, inv_inv, mul_assoc]

variable [TopologicalSpace K] [TopologicalSpace R] [IsTopologicalRing R] [IsModuleTopology K R]

private theorem continuous_radicalLeviAction (U : M) : Continuous (radicalLeviAction h U) :=
  (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const

theorem continuous_twistedRadicalDifference (D : M) : Continuous (twistedRadicalDifference σ h D) :=
  (continuous_id.matrix_map (IsModuleTopology.continuous_of_linearMap σ.toLinearMap)).sub
    (continuous_radicalLeviAction h D⁻¹)

end Algebra

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

local instance twistedRadicalFieldMeasurable {p : ℕ} [Fact p.Prime] (K : PadicField.{v} p) :
    MeasurableSpace K.Carrier := borel _
local instance twistedRadicalFieldBorel {p : ℕ} [Fact p.Prime] (K : PadicField.{v} p) :
    BorelSpace K.Carrier := ⟨rfl⟩
local instance twistedRadicalFieldSecondCountable {p : ℕ} [Fact p.Prime] (K : PadicField.{v} p) :
    SecondCountableTopology K.Carrier := K.canonicalTopologicalData.secondCountableTopology

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
    [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
    [IsModuleTopology F.Carrier E.Carrier]
    (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier)
    {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "M" => BlockShape.Levi B E.Carrier
local notation "Rect" => Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) E.Carrier

set_option maxHeartbeats 1000000 in
/-- The scalar of the radical change of variables is unchanged after a twisted
conjugation by a Levi element. -/
theorem map_twistedRadicalDifference_twistedConj (D U : M)
    (dx : Measure Rect) [dx.IsAddHaarMeasure] (c : ℝ≥0)
    (hc : Measure.map (twistedRadicalDifference σ h D) dx = c • dx) :
    Measure.map (twistedRadicalDifference σ h (U⁻¹ * D * leviAut σ B U)) dx = c • dx := by
  let T := E.canonicalTopologicalData
  let s (V : M) : ℝ≥0 := (((T.determinantNorm (m 0 + 1) (V 0) : ℝ≥0) ^ (m 1 + 1) /
    (T.determinantNorm (m 1 + 1) (V 1) : ℝ≥0) ^ (m 0 + 1)))⁻¹
  have hMap (V : M) : Measure.map (radicalLeviAction h V) dx = s V • dx :=
    padicRectangularHaarScaling E T (m 0 + 1) (m 1 + 1) dx (V 0) (V 1)
  have hs : s (leviAut σ B U) = s U := by
    simp only [s, T, leviAut_apply, padicDeterminantNorm_entrywiseAut F E σ]
  have hm (V : M) : Measurable (radicalLeviAction h V) := (continuous_radicalLeviAction h V).measurable
  have hD : Measurable (twistedRadicalDifference σ h D) :=
    (continuous_twistedRadicalDifference σ h D).measurable
  have hCancel : radicalLeviAction h (leviAut σ B U)⁻¹ ∘ radicalLeviAction h (leviAut σ B U) =
      (id : Rect → Rect) := by
    funext x
    simp only [Function.comp_apply, ← radicalLeviAction_mul, inv_mul_cancel, radicalLeviAction_one, id]
  rw [twistedRadicalDifference_twistedConj σ h D U,
    ← Measure.map_map (hm _) (hD.comp (hm U)), ← Measure.map_map hD (hm U),
    hMap U, Measure.map_smul _ hD.aemeasurable, hc, smul_comm (s U) c, ← hs, ← hMap,
    Measure.map_smul _ (hm _).aemeasurable, Measure.map_map (hm _) (hm _), hCancel, Measure.map_id]

end Langlands.BaseChange
