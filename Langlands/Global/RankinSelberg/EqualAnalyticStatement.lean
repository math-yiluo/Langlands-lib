import Langlands.Global.RankinSelberg.EisensteinStatement

/-! # The global analytic theory for equal-rank cuspidal pairs

For cuspidal realizations `T`, `T'` of `GL_n`, `n = r + 1`, with central characters `ω`, `ω'`,
`η = ω ω'`, a nontrivial unitary character `ψ` of `F \ 𝔸` and `Φ ∈ S(𝔸^n)`: the integral
`I(s; φ, φ', Φ)` converges absolutely on a right half-plane, continues to a function
holomorphic off the finite set `P(η)` with at most simple poles there, is bounded in vertical
strips away from `P(η)`, and satisfies `I(s; φ, φ', Φ) = I(1 - s; φ̃, φ̃', Φ̂)`
(Cogdell 2004, Theorem 2.2, p.211).
-/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

local instance equalAnalyticSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalAnalyticSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

/-- Uniform boundedness on every closed vertical strip with the `δ`-neighbourhoods of the
points of `P` removed. -/
def BoundedInVerticalStripsAwayFrom (f : ℂ → ℂ) (P : Set ℂ) : Prop :=
  ∀ a b : ℝ, a ≤ b → ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ s : ℂ, a ≤ s.re → s.re ≤ b → (∀ p ∈ P, δ ≤ ‖s - p‖) → ‖f s‖ ≤ C

/-- Cogdell 2004, Theorem 2.2, printed p.211: the analytic and functional-equation clauses
for `m = n`, with `η = ω ω'` written `ω * ω'`. Every convergence and analytic assertion is in
the conclusion. -/
def EqualAnalyticStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ),
    T.realization.HasCentralCharacter ω → T'.realization.HasCentralCharacter ω' →
    ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space) (Φ : RowVector F (r + 1) → ℂ),
      Φ ∈ schwartzBruhat F (r + 1) →
      let φ := cuspFunction F T v
      let φ' := cuspFunction F T' v'
      let φdual := dualFunction F (r + 1) φ
      let φ'dual := dualFunction F (r + 1) φ'
      let Φhat := fourierTransform F (r + 1) ψ Φ
      ∃ σ₀ : ℝ, ∃ I Idual : ℂ → ℂ,
        (∀ s : ℂ, σ₀ < s.re →
          Integrable (equalIntegrand F (ω * ω') φ φ' Φ s) (centralQuotientMeasure F (r + 1)) ∧
          Integrable (equalIntegrand F (ω * ω')⁻¹ φdual φ'dual Φhat s)
            (centralQuotientMeasure F (r + 1)) ∧
          I s = equalIntegral F (ω * ω') φ φ' Φ s ∧
          Idual s = equalIntegral F (ω * ω')⁻¹ φdual φ'dual Φhat s) ∧
        HasAtMostSimplePolesIn I (equalPoleSet F (r + 1) (ω * ω')) ∧
        HasAtMostSimplePolesIn Idual (equalPoleSet F (r + 1) (ω * ω')⁻¹) ∧
        BoundedInVerticalStripsAwayFrom I (equalPoleSet F (r + 1) (ω * ω')) ∧
        ∀ s : ℂ, s ∉ equalPoleSet F (r + 1) (ω * ω') → I s = Idual (1 - s)

end Langlands.Global.RankinSelbergGlobal
