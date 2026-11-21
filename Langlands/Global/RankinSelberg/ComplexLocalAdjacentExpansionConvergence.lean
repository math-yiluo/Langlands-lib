import Langlands.Global.RankinSelberg.ComplexAdjacentConvergence
import Langlands.Global.RankinSelberg.ComplexLocalAdjacentUnfolding

/-!
# Convergence for the corank-one expansion kernel
-/

noncomputable section

open MeasureTheory
open Langlands GeneralLinear LocalFactor.Archimedean QuotientIntegration RankinSelberg
open scoped Matrix.Norms.Operator SchwartzMap

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquet

open ArchimedeanLocal

set_option autoImplicit false

attribute [local instance] archimedeanEquationComplexGLMeasurable
  archimedeanEquationComplexGLBorel archimedeanEquationComplexNMeasurable
  archimedeanEquationComplexNBorel archimedeanEquationComplexQMeasurable
  archimedeanEquationComplexQBorel

variable {r : ℕ}

local notation "H" => Langlands.GeneralLinear (r + 1) ℂ
local notation "Q" => LeftUnipotentQuotient r ℂ
local notation "Mat" => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ
local notation "Row" => Fin (r + 1) → ℂ

local instance adjacentExpansionGLSecondCountable :
    SecondCountableTopology H :=
  Units.isOpenEmbedding_val.isEmbedding.secondCountableTopology

local instance adjacentExpansionQuotientSigmaCompact : SigmaCompactSpace Q := by
  have hq := leftQuotient_isOpenQuotientMap (Langlands.GeneralLinear.upperUnipotent (r + 1) ℂ)
  apply isSigmaCompact_univ_iff.mp
  rw [← Set.range_eq_univ.mpr hq.surjective]
  exact isSigmaCompact_range hq.continuous

theorem complexLocalGroupHaarSigmaFinite (D : ComplexQuotientMeasureData r) :
    SigmaFinite D.groupHaar := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  infer_instance

theorem complexLocalQuotientSigmaFinite (D : ComplexQuotientMeasureData r) :
    SigmaFinite D.measure := by
  let : D.unipotentHaar.IsMulRightInvariant := D.unipotentHaar_rightInvariant
  let : D.measure.Regular := D.compatible.regular
  infer_instance

private theorem detPower_eq_normPower (s : ℂ) (g : H) :
    ArchimedeanLocal.detPower complexNormalizedAbs g s =
      ComplexGodement.normPower s (determinant g) := by
  let A := complexNormalizedAbs g.val.det
  have hA : 0 < A := pow_pos (norm_pos_iff.mpr g.det_ne_zero) _
  change Complex.exp (s * (Real.log A : ℂ)) = (A : ℂ) ^ s
  rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hA.ne'),
    ← Complex.ofReal_log hA.le, mul_comm]

/-- Absolute convergence of the corank-one expansion kernel in quotient-first order. -/
def ComplexLocalAdjacentExpansionConvergenceStatement : Prop :=
  ∀ (D : ComplexQuotientMeasureData r) (d : ComplexCharacterData)
    (Φ₁ : 𝓢(Mat, ℂ)) (Φ₂ : 𝓢(Row, ℂ)) (a : ℂˣ) (ds es : List ComplexCharacterData)
    (U : complexWhittakerModel r ds a) (V : complexWhittakerModel r es (-a)),
    ∃ σ : ℝ, ∀ s : ℂ, σ < s.re →
      Integrable (complexAdjacentUnfoldedKernel d.character Φ₁ Φ₂ U.val V.val s)
        (D.measure.prod D.groupHaar)

theorem complexLocalAdjacentExpansionConvergence :
    ComplexLocalAdjacentExpansionConvergenceStatement (r := r) := by
  intro D d Φ₁ Φ₂ a ds es U V
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : SigmaFinite D.groupHaar := complexLocalGroupHaarSigmaFinite D
  let : SigmaFinite D.measure := complexLocalQuotientSigmaFinite D
  obtain ⟨σ, hσ⟩ := ComplexAdjacentUnfolding.complexAdjacentConvergence
    D D.groupHaar d ((r : ℂ) / 2) Φ₁ Φ₂ a ds es U V
  refine ⟨σ, fun s hs => (hσ s hs).swap.congr (Filter.Eventually.of_forall ?_)⟩
  rintro ⟨q, g⟩
  let F := complexEqualIntegrand U.val (fun x => V.val (x * g)) Φ₂ s q
  change Φ₁ g.val * ((d.character (determinant g) : ℂ) *
      ComplexGodement.normPower ((r : ℂ) / 2 + s) (determinant g)) * F =
    F * (Φ₁ g.val * (d.character (determinant g) : ℂ) *
      ArchimedeanLocal.detPower complexNormalizedAbs g (s + (r : ℂ) / 2))
  rw [← detPower_eq_normPower, add_comm ((r : ℂ) / 2) s]
  ac_rfl

end Langlands.Global.RankinSelbergGlobal.ComplexJacquet
