import Langlands.Global.RankinSelberg.ComplexAdjacentConvergence
import Langlands.Global.RankinSelberg.ComplexAdjacentSplitFourier
import Langlands.Global.RankinSelberg.ComplexGodementContinuedReflection
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentIntegrals

/-! # The ordinary and dual adjacent-rank integrals of a split Godement value -/

noncomputable section

open MeasureTheory
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding

open ArchimedeanLocal (ComplexQuotientMeasureData complexSelfDualMeasure
  complexUnequalIntegral complexUnequalDualIntegral)
open Langlands.Analysis.SchwartzMatrixNorm (operatorToEntry)
open Langlands.GeneralLinear Langlands.GodementJacquet Langlands.LocalFactor.Archimedean
open ComplexGodement (characterWeight)
open ComplexGodementAddedCharacter (continuedValue complexGodementContinuedReflection)
open ComplexLocalWhittakerDual (dualData dualFunction_mem)
open ComplexJacquet (complexUnequalDualIntegral_adjacent)

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "G" => Langlands.GeneralLinear (r + 1 + 1) ℂ
local notation "N" => Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Vec" => Fin (r + 1) → ℂ
local notation "dualH" => ArchimedeanLocal.dualFunction (r + 1)
local notation "dualG" => ArchimedeanLocal.dualFunction (r + 1 + 1)
local notation "pad" => padGL (Nat.le_succ (r + 1))
local notation "gap" => Nat.lt_succ_self r
local notation "columnProd" => ComplexGodementColumnProduct.columnProduct

/-- The Haar measure of a compatible complex quotient datum is also right invariant. -/
theorem complexAdjacent_groupHaar_rightInvariant (D : ComplexQuotientMeasureData r) :
    D.groupHaar.IsMulRightInvariant := by
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : LocallyCompactSpace Mat :=
    inferInstanceAs (LocallyCompactSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
  let : BorelSpace Mat := inferInstanceAs (BorelSpace (Fin (r + 1) → Fin (r + 1) → ℂ))
  let μ := Measure.addHaarMeasure (Classical.arbitrary (TopologicalSpace.PositiveCompacts Mat))
  let : μ.IsAddHaarMeasure := Measure.isAddHaarMeasure_addHaarMeasure _
  let μH := complexMatrixHaar (r + 1) μ
  let : μH.IsHaarMeasure := complexMatrixHaar_isHaar (r + 1) μ
  let : μH.IsMulRightInvariant := complexMatrixHaar_isMulRightInvariant (r + 1) μ
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  rw [Measure.isMulLeftInvariant_eq_smul D.groupHaar μH]
  infer_instance

/-- The actual adjacent ordinary and dual integrals of the continued split
Godement value are absolutely convergent unfolded products in a right half-plane. -/
def ComplexAdjacentSplitIntegralsStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) [SFinite D.measure]
    (a : ℂˣ) (d : ComplexCharacterData) (p : ℂ) (Φ : 𝓢(Mat, ℂ)) (φ : 𝓢(Vec, ℂ))
    (ds es : List ComplexCharacterData), ds.length = r + 1 → es.length = r + 1 →
  ∀ (U : complexWhittakerModel r ds (-a)) (V : complexWhittakerModel r es a),
    let W : G → ℂ := fun g => continuedValue D.groupHaar (complexSelfDualMeasure a) d a
      (operatorToEntry (columnProd Φ φ)) U.val g p
    let I := fun s => unfoldedKernel d (p + (r : ℂ) / 2) s Φ (splitRowTransform a φ) U.val V.val
    let J := fun s => unfoldedKernel d.inv (-p + (r : ℂ) / 2) s (splitSquareTransform a Φ)
      φ (dualH U.val) (dualH V.val)
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (I s) (D.groupHaar.prod D.measure) ∧
      Integrable (J s) (D.groupHaar.prod D.measure) ∧
      complexUnequalIntegral gap D W V.val s =
        (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) * ∫ x, I s x ∂D.groupHaar.prod D.measure ∧
      complexUnequalDualIntegral gap (-a) D W V.val s =
        ∫ x, J s x ∂D.groupHaar.prod D.measure

theorem complexAdjacentSplitIntegrals : ComplexAdjacentSplitIntegralsStatement (r := r) := by
  intro D _ a d p Φ φ ds es hds hes U V W I J
  let e := Langlands.RankinSelberg.isOpenEmbedding_generalLinear_val (K := ℂ) (r + 1)
  let : LocallyCompactSpace H := e.locallyCompactSpace
  let : SecondCountableTopology H := e.secondCountableTopology
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := complexAdjacent_groupHaar_rightInvariant D
  let V₀ : complexWhittakerModel r es (-(-a)) := ⟨V.val, by simpa only [neg_neg] using V.2⟩
  let Ud : complexWhittakerModel r (dualData ds) a :=
    ⟨dualH U.val, by simpa only [neg_neg] using dualFunction_mem hds U.2⟩
  let Vd : complexWhittakerModel r (dualData es) (-a) := ⟨dualH V.val, dualFunction_mem hes V.2⟩
  obtain ⟨σ, hσ⟩ := complexAdjacentConvergence D D.groupHaar d (p + (r : ℂ) / 2)
    Φ (splitRowTransform a φ) (-a) ds es U V₀
  obtain ⟨τ, hτ⟩ := complexAdjacentConvergence D D.groupHaar d.inv (-p + (r : ℂ) / 2)
    (splitSquareTransform a Φ) φ a (dualData ds) (dualData es) Ud Vd
  have hU (u : N) (g : H) :=
    complexWhittakerModel_left_equivariant U.2 u.val u.2 g
  have hV (u : N) (g : H) :=
    complexWhittakerModel_left_equivariant V₀.2 u.val u.2 g
  have hUd (u : N) (g : H) :=
    complexWhittakerModel_left_equivariant Ud.2 u.val u.2 g
  have hVd (u : N) (g : H) :=
    complexWhittakerModel_left_equivariant Vd.2 u.val u.2 g
  have hW (g : H) : W (pad g) =
      (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
        characterWeight d (p + (r : ℂ) / 2 + 1 / 2) (determinant g) *
          ∫ h, Φ (h * g).val * splitRowTransform a φ (Langlands.RankinSelberg.lastRow h⁻¹) *
            U.val h⁻¹ * characterWeight d (p + (r : ℂ) / 2) (determinant h) ∂D.groupHaar := by
    simpa only [W, splitRowTransform_apply] using
      complexAdjacentSplitRestriction D.groupHaar (complexSelfDualMeasure a) d a Φ φ U.val p g
  obtain ⟨hFourier, hRow⟩ := complexAdjacentSplitFourier a Φ φ
  have hWd (g : H) : dualG W (pad g) =
      (1 : ℂ) * characterWeight d.inv (-p + (r : ℂ) / 2 + 1 / 2) (determinant g) *
        ∫ h, splitSquareTransform a Φ (h * g).val * φ (Langlands.RankinSelberg.lastRow h⁻¹) *
          Ud.val h⁻¹ * characterWeight d.inv (-p + (r : ℂ) / 2) (determinant h) ∂D.groupHaar := by
    have h := complexGodementContinuedReflection D a d (operatorToEntry (columnProd Φ φ))
      (operatorToEntry (columnProd (splitSquareTransform a Φ) (splitRowTransform a φ)))
      hFourier ds hds U (pad g) p
    change dualG W (pad g) = (d.character ((-1 : ℂˣ) ^ (r + 1)) : ℂ) *
      continuedValue D.groupHaar (complexSelfDualMeasure a) d.inv (-a)
        (operatorToEntry (columnProd (splitSquareTransform a Φ) (splitRowTransform a φ)))
        Ud.val (pad g) (-p) at h
    rw [h, complexAdjacentSplitRestriction D.groupHaar (complexSelfDualMeasure a) d.inv (-a)
      (splitSquareTransform a Φ) (splitRowTransform a φ) Ud.val (-p) g]
    simp only [hRow, ComplexCharacterData.inv_character_apply, ← mul_assoc,
      mul_inv_cancel₀ (d.character ((-1 : ℂˣ) ^ (r + 1))).ne_zero]
  refine ⟨max σ τ, fun s hs => ?_⟩
  have hI : Integrable (I s) (D.groupHaar.prod D.measure) :=
    hσ s ((le_max_left σ τ).trans_lt hs)
  have hJ : Integrable (J s) (D.groupHaar.prod D.measure) :=
    hτ s ((le_max_right σ τ).trans_lt hs)
  refine ⟨hI, hJ, ?_, ?_⟩
  · exact complexAdjacentUnfolding D D.groupHaar d (p + (r : ℂ) / 2) s Φ
      (splitRowTransform a φ) (-a) U.val V₀.val W _ hU hV hW hI
  · rw [complexUnequalDualIntegral_adjacent]
    simpa only [one_mul] using complexAdjacentUnfolding D D.groupHaar d.inv (-p + (r : ℂ) / 2) s
      (splitSquareTransform a Φ) φ a Ud.val Vd.val (dualG W) 1 hUd hVd hWd hJ

end Langlands.Global.RankinSelbergGlobal.ComplexAdjacentUnfolding
