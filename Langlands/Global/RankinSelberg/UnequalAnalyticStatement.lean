import Langlands.Global.RankinSelberg.UnequalIntegrals
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! # The global analytic theory for unequal-rank cuspidal pairs -/

noncomputable section
universe u
open NumberField MeasureTheory
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance analyticSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance analyticSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- A nontrivial continuous unitary character of the adeles, trivial on the number field. -/
def IsStandardAdditiveCharacter (F : Type u) [Field F] [NumberField F]
    (ψ : AddChar (Adeles F) ℂ) : Prop :=
  Continuous ψ ∧ ψ ≠ 1 ∧
    (∀ x : F, ψ (algebraMap F (Adeles F) x) = 1) ∧
    ∀ x : Adeles F, ‖ψ x‖ = 1

/-- Uniform boundedness on every closed vertical strip, with no excluded points. -/
def BoundedInVerticalStrips (f : ℂ → ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → ‖f s‖ ≤ C

/-- Cogdell 2004, Theorem 2.1, analytic and functional-equation clauses.
Every convergence and analytic assertion is in the conclusion. -/
def UnequalAnalyticStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t)
    (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space),
      let φ := cuspFunction F T v
      let φ' := cuspFunction F T' v'
      let φdual := dualFunction F (r + 1) φ
      let φ'dual := dualFunction F (t + 1) φ'
      let I := unequalIntegral F h ψ φ φ'
      (∀ s : ℂ, Integrable (unequalIntegrand F h ψ φ φ' s)
        (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)))) ∧
      (∀ s : ℂ, Integrable (dualUnequalIntegrand F h ψ φdual φ'dual s)
        (AdelicGroupPoints.rationalQuotientHaarMeasure F (Scheme F (t + 1)))) ∧
      Differentiable ℂ I ∧ BoundedInVerticalStrips I ∧
      ∀ s : ℂ, I s = dualUnequalIntegral F h ψ φdual φ'dual (1 - s)

end Langlands.Global.RankinSelbergGlobal
