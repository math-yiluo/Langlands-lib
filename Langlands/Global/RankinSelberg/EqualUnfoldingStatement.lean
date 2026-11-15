import Langlands.Global.RankinSelberg.EqualIntegrals
import Langlands.Global.RankinSelberg.UnequalAnalyticStatement

/-! # Unfolding the global integrals of equal-rank cuspidal pairs

For cuspidal realizations `T`, `T'` of `GL_n`, `n = r + 1`, with central characters `ω`, `ω'`
and `η = ω ω'`: on a right half-plane depending only on `T` and `T'`,
`I(s; φ, φ', Φ) = Ψ(s; W_φ, W'_φ', Φ)`, and on the opposite left half-plane
`I(1 - s; φ̃, φ̃', Φ̂) = Ψ(1 - s; W̃_φ, W̃'_φ', Φ̂)`, with absolutely convergent integrals on
both sides (Cogdell 2004, §2.3, pp.210–211).
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalUnfoldingSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalUnfoldingSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- Cogdell 2004, §2.3, printed pp.210–211: unfolding of the equal-rank global integral and
of the right-hand side of its functional equation, with a half-plane bound depending only on
the two cuspidal realizations. `η = ω ω'` is written `ω * ω'`. -/
def EqualUnfoldingStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ),
    T.realization.HasCentralCharacter ω → T'.realization.HasCentralCharacter ω' →
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
        ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
          Φ ∈ schwartzBruhat F (r + 1) →
          let φ := cuspFunction F T v
          let φ' := cuspFunction F T' v'
          let W := cuspWhittaker F T ψ v
          let W' := cuspWhittaker F T' ψ⁻¹ v'
          let φdual := dualFunction F (r + 1) φ
          let φ'dual := dualFunction F (r + 1) φ'
          let Wdual := dualFunction F (r + 1) W
          let W'dual := dualFunction F (r + 1) W'
          let Φhat := fourierTransform F (r + 1) ψ Φ
          (∀ s : ℂ, C < s.re →
            Integrable (equalIntegrand F (ω * ω') φ φ' Φ s)
              (centralQuotientMeasure F (r + 1)) ∧
            Integrable (equalWhittakerIntegrand F W W' Φ s)
              (whittakerQuotientMeasure F (r + 1)) ∧
            equalIntegral F (ω * ω') φ φ' Φ s = equalWhittakerIntegral F W W' Φ s) ∧
          ∀ s : ℂ, s.re < -C →
            Integrable (equalIntegrand F (ω * ω')⁻¹ φdual φ'dual Φhat (1 - s))
              (centralQuotientMeasure F (r + 1)) ∧
            Integrable (equalWhittakerIntegrand F Wdual W'dual Φhat (1 - s))
              (whittakerQuotientMeasure F (r + 1)) ∧
            equalIntegral F (ω * ω')⁻¹ φdual φ'dual Φhat (1 - s) =
              equalWhittakerIntegral F Wdual W'dual Φhat (1 - s)

end Langlands.Global.RankinSelbergGlobal
