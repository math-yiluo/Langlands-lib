import Langlands.Global.RankinSelberg.WhittakerIntegrals
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Unfolding the global integrals of unequal-rank cuspidal pairs -/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance unfoldingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance unfoldingSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance unfoldingRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

/-- Absolute convergence of the iterated dual integral, including the inner
integrals and the integral of their absolute values. -/
def DualWhittakerAbsolutelyConvergent (F : Type u) [Field F] [NumberField F]
    {r t : ℕ} (h : t < r)
    (W : Points F (r + 1) → ℂ) (W' : Points F (t + 1) → ℂ) (s : ℂ) : Prop :=
  (∀ᵐ q ∂whittakerQuotientMeasure F (t + 1),
    Integrable (dualWhittakerKernel F h W W' s q)
      (rectangleMeasure F (r - (t + 1)) (t + 1))) ∧
  Integrable
    (fun q => ∫ x, ‖dualWhittakerKernel F h W W' s q x‖
      ∂rectangleMeasure F (r - (t + 1)) (t + 1))
    (whittakerQuotientMeasure F (t + 1)) ∧
  Integrable (dualWhittakerIntegrand F h W W' s)
    (whittakerQuotientMeasure F (t + 1))

/-- Cogdell 2004, pp.205–207: ordinary and dual unfolding, with a
half-plane bound depending only on the two actual cuspidal realizations. -/
def UnequalUnfoldingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
        ∀ (v : T.Space) (v' : T'.Space),
          let φ := cuspFunction F T v
          let φ' := cuspFunction F T' v'
          let W := cuspWhittaker F T ψ v
          let W' := cuspWhittaker F T' ψ⁻¹ v'
          let Wdual := translateFunction F (r + 1) (unfoldingWeyl F h)
            (dualFunction F (r + 1) W)
          let W'dual := dualFunction F (t + 1) W'
          (∀ s : ℂ, C < s.re →
            Integrable (unequalWhittakerIntegrand F h W W' s)
              (whittakerQuotientMeasure F (t + 1)) ∧
            unequalIntegral F h ψ φ φ' s =
              unequalWhittakerIntegral F h W W' s) ∧
          ∀ s : ℂ, s.re < -C →
            DualWhittakerAbsolutelyConvergent F h Wdual W'dual (1 - s) ∧
            dualUnequalIntegral F h ψ
              (dualFunction F (r + 1) φ) (dualFunction F (t + 1) φ') (1 - s) =
                dualWhittakerIntegral F h Wdual W'dual (1 - s)

end Langlands.Global.RankinSelbergGlobal
