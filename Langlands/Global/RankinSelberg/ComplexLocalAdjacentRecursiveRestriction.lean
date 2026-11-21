import Langlands.Analysis.SchwartzMatrixNorm
import Langlands.Global.RankinSelberg.ComplexGodementColumnProduct
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentUnfolding
import Langlands.Global.RankinSelberg.ComplexLocalEqualMeromorphicReduction
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerDual
import Langlands.Global.RankinSelberg.ComplexLocalWhittakerRegularity
import Langlands.Representation.GodementJacquet.ComplexJacquetRecursionConvergence
import Langlands.Representation.GodementJacquet.ComplexTriangularMatchedTests

/-! # Exact restricted complex recursions for the adjacent-rank unfolding -/

noncomputable section

open MeasureTheory
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean
open Langlands.Analysis.SchwartzMatrixNorm (OperatorSchwartz operatorToEntry)
open scoped Matrix.Norms.Elementwise SchwartzMap

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal
open ComplexCharacterChange (model_unipotent_mul)
open ComplexGodementColumnProduct (columnProduct rectangularFourierIntegral_column_mul)
open ComplexLocalWhittakerDual (dualData dualFunction_mem length_dualData)

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "m" => r + 1
local notation "n" => (r + 1) + 1
local notation "H" => Langlands.GeneralLinear m ℂ
local notation "G" => Langlands.GeneralLinear n ℂ
local notation "Mat" => Matrix (Fin m) (Fin m) ℂ
local notation "Rect" => Matrix (Fin m) (Fin n) ℂ
local notation "Row" => Fin m → ℂ
local notation "pad" => padGL (R := ℂ) (Nat.succ_le_succ (Nat.le_succ r))
local notation "sm" => ((m : ℕ) : ℂ) / 2
local notation "sn" => ((n : ℕ) : ℂ) / 2
local notation "P" => ArchimedeanLocal.detPower complexNormalizedAbs
local notation "ud" => ArchimedeanLocal.dualFunction m
local notation "wd" => ArchimedeanLocal.dualFunction n

private theorem rectangularJoin_mul_pad (X : Mat) (z : Row) (g : H) :
    rectangularJoin X z * (pad g).val = rectangularJoin (X * g.val) z := by
  ext i j
  refine Fin.lastCases ?_ (fun j => ?_) j
  · rw [Matrix.mul_apply, Fin.sum_univ_castSucc, rectangularJoin_last]
    simp [UnequalAnalytic.padGL_apply, Fin.castSucc_ne_last]
  · rw [Matrix.mul_apply, Fin.sum_univ_castSucc, rectangularJoin_castSucc, Matrix.mul_apply]
    have hle (i : Fin m) : i.val ≤ r := Nat.le_of_lt_succ i.isLt
    simp [UnequalAnalytic.padGL_apply, hle, Ne.symm (Fin.castSucc_ne_last j)]

private theorem columnFourier_mul (a : ℂˣ) (Φ : Mat → ℂ) (χ : Row → ℂ)
    (X : Mat) (y : Row) :
    complexLastColumnFourier a (fun Z => Φ (rectangularFirstColumns Z) * χ (rectangularLastColumn Z)) X y =
      Φ X * complexFourierTransform a χ y := by
  unfold complexLastColumnFourier
  simp only [rectangularFirstColumns_join, rectangularLastColumn_join, mul_assoc, integral_const_mul,
    complexFourierTransform, ArchimedeanLocal.fourierTransform]
  congr 1
  refine integral_congr_ae (ae_of_all _ fun z => ?_)
  unfold complexCoordinatePair
  simp only [mul_comm (y _)]

private theorem squareFourier_neg_parameter (a : ℂˣ) (Φ : Mat → ℂ) (Y : Mat) :
    complexMatrixFourier (-a) Φ Y = complexMatrixFourier a Φ (-Y) := by
  change (∫ X : Mat, Φ X * traceCharacter (-a) (rectangularPairing X Y)
      ∂(RankinSelberg.rectangularMeasure (complexSelfDualMeasure (-a)) m m)) =
    ∫ X : Mat, Φ X * traceCharacter a (rectangularPairing X (-Y))
      ∂(RankinSelberg.rectangularMeasure (complexSelfDualMeasure a) m m)
  rw [complexSelfDualMeasure_neg_scale]
  refine integral_congr_ae (ae_of_all _ fun X => ?_)
  dsimp only
  rw [traceCharacter_neg_scale]
  simp only [rectangularPairing, Matrix.neg_apply, mul_neg, ← Finset.sum_neg_distrib]

open scoped Matrix.Norms.Operator in
private theorem continuous_smallerVector {ds : List ComplexCharacterData} {a : ℂˣ}
    (U : complexWhittakerModel r ds a) : Continuous U.val :=
  (contMDiff_of_mem_complexWhittakerModel U.2).continuous

private theorem restricted_recursion_group (a : ℂˣ) (D : ComplexQuotientMeasureData r)
    (d : ComplexCharacterData) (ds : List ComplexCharacterData) (hds : ds.length = m)
    (U : complexWhittakerModel r ds a) (F : 𝓢(Rect, ℂ)) (Φ : Mat → ℂ) (χ : Row → ℂ)
    (hF : (F : Rect → ℂ) = fun X => Φ (rectangularFirstColumns X) * χ (rectangularLastColumn X))
    (g : H) :
    complexJacquetRecursion a D F U.val d.character.toMonoidHom (pad g) =
      ∫ k, complexAdjacentRestrictionKernel d.character Φ (complexFourierTransform (-a) χ)
        U.val g k ∂D.groupHaar := by
  have hU := complexLocalWhittakerSimpleRootBound_of_uniformGrowth complexLocalWhittakerUniformGrowth
    r ds hds a U.val U.2
  rw [complexJacquetRecursion_eq_group_of_simpleRootLogBound a D F d (continuous_smallerVector U)
    (fun u k => model_unipotent_mul U.2 u k) hU]
  refine integral_congr_ae (ae_of_all _ fun k => ?_)
  have ht : (fun X : Rect => F (X * (pad g).val)) =
      fun X => Φ (rectangularFirstColumns X * g.val) * χ (rectangularLastColumn X) := by
    funext X
    conv_lhs => rw [← rectangularJoin_split X]
    rw [rectangularJoin_mul_pad, hF]
    simp only [rectangularFirstColumns_join, rectangularLastColumn_join]
  have hd : GeneralLinear.determinant (pad g) = GeneralLinear.determinant g :=
    Units.ext (UnequalAnalytic.det_padGL _ _)
  have hPower : P (pad g) sm = P g sm := by
    simp only [ArchimedeanLocal.detPower, UnequalAnalytic.det_padGL]
  have hshift : sn - 1 = (r : ℂ) / 2 := by push_cast; ring
  change complexJacquetRecursionGroupKernel a F U.val d.character.toMonoidHom (pad g) k = _
  unfold complexJacquetRecursionGroupKernel
  rw [ht, columnFourier_mul (-a) (fun X : Mat => Φ (X * g.val)) χ, hshift]
  have hWeight : complexJacquetDetWeight d.character.toMonoidHom (pad g) sm =
      (d.character (GeneralLinear.determinant g) : ℂ) * P g sm := by
    change (d.character (GeneralLinear.determinant (pad g)) : ℂ) * P (pad g) sm = _
    rw [hd, hPower]
  rw [hWeight, complexJacquetDetWeight]
  change _ = (d.character (GeneralLinear.determinant g) : ℂ) * P g sm *
    Φ ((k⁻¹ * g).val) * complexFourierTransform (-a) χ (RankinSelberg.lastRow k) * U.val k *
    (d.character (GeneralLinear.determinant k⁻¹) : ℂ) * P k⁻¹ ((r : ℂ) / 2)
  rw [Units.val_mul]
  change (d.character (GeneralLinear.determinant g) : ℂ) * P g sm *
    (Φ ((k⁻¹).val * g.val) * complexFourierTransform (-a) χ (RankinSelberg.lastRow k)) * U.val k *
    ((d.character (GeneralLinear.determinant k⁻¹) : ℂ) * P k⁻¹ ((r : ℂ) / 2)) = _
  ring

/-- The separated rectangular recursion and its exact dual give the two
restricted kernels needed by the corank-one unfolding. -/
def ComplexLocalAdjacentRecursiveRestrictionStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (a : ℂˣ) (d : ComplexCharacterData)
    (ds : List ComplexCharacterData), ds.length = m →
  ∀ (U : complexWhittakerModel r ds a) (Φ : OperatorSchwartz m m) (χ : 𝓢(Row, ℂ)),
    let F := operatorToEntry (columnProduct Φ χ)
    let W := complexJacquetRecursion a D F U.val d.character.toMonoidHom
    let φ := complexFourierTransform (-a) χ
    (∀ g : H, W (pad g) =
      ∫ k, complexAdjacentRestrictionKernel d.character Φ φ U.val g k ∂D.groupHaar) ∧
    (∀ g : H, wd W (pad g) =
      (d.character (-1) : ℂ) ^ m *
        ∫ k, complexAdjacentRestrictionKernel d.inv.character (fun X => complexMatrixFourier a Φ (-X))
          (complexFourierTransform a φ) (ud U.val) g k ∂D.groupHaar)

set_option maxHeartbeats 1000000 in
theorem complexLocalAdjacentRecursiveRestriction :
    ComplexLocalAdjacentRecursiveRestrictionStatement (r := r) := by
  intro D a d ds hds U Φ χ F W φ
  have hF : (F : Rect → ℂ) = fun X => Φ (rectangularFirstColumns X) * χ (rectangularLastColumn X) := rfl
  refine ⟨restricted_recursion_group a D d ds hds U F Φ χ hF, ?_⟩
  obtain ⟨Fd, hFd⟩ := exists_schwartz_complexRectangularFourier (-a) F
  have hSeparated : (Fd : Rect → ℂ) =
      fun X => complexMatrixFourier a Φ (-rectangularFirstColumns X) * φ (rectangularLastColumn X) := by
    funext Y
    have : (complexSelfDualMeasure (-a)).measure.IsAddHaarMeasure := (complexSelfDualMeasure (-a)).isAddHaar
    rw [hFd, hF]
    have he := rectangularFourierIntegral_column_mul (complexScaledCharacter (-a))
      (complexSelfDualMeasure (-a)) Φ χ Y
    change complexRectangularFourier (-a)
      (fun X : Rect => Φ (rectangularFirstColumns X) * χ (rectangularLastColumn X)) Y =
      complexMatrixFourier (-a) Φ (rectangularFirstColumns Y) *
      complexFourierTransform (-a) χ (rectangularLastColumn Y) at he
    rw [he, squareFourier_neg_parameter]
  let Ud : complexWhittakerModel r (dualData ds) (-a) := ⟨ud U.val, dualFunction_mem hds U.2⟩
  have hd : d.inv.character.toMonoidHom = d.character.toMonoidHom.comp invMonoidHom := by
    apply MonoidHom.ext
    intro z
    change (d.character z)⁻¹ = d.character z⁻¹
    exact (map_inv d.character z).symm
  intro g
  have hdual := complexJacquetRecursion_dual a D F U.val d.character.toMonoidHom
    (fun u k => model_unipotent_mul U.2 u k) (pad g)
  rw [← hFd, ← hd] at hdual
  have hgroup := restricted_recursion_group (-a) D d.inv (dualData ds)
    ((length_dualData ds).trans hds) Ud Fd (fun X => complexMatrixFourier a Φ (-X)) φ hSeparated g
  rw [neg_neg] at hgroup
  exact hdual.trans (congrArg (_ * ·) hgroup)

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
