import Langlands.Global.RankinSelberg.UnfoldingDual

/-! # A conditional reduction of the unequal-rank unfolding statement

The Library statement `UnequalUnfoldingStatement` (Cogdell 2004, pp.205–207) follows from four
explicitly stated analytic premises for each pair of cuspidal realizations: the Whittaker
expansion of the projection, its dual analogue, and two gauge-type integrability claims. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal

open Unfolding

local instance reductionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance reductionSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local instance reductionRectangleMeasurableSpace (F : Type u) [Field F]
    [NumberField F] (k m : ℕ) :
    MeasurableSpace (Matrix (Fin k) (Fin m) (Adeles F)) := borel _

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

/-- Gauge integrability (Cogdell 2004, p.206): for `Re s` beyond a bound depending only on the
realizations, `h ↦ W_φ(diag(h, I)) φ'(h) |det h|^(s-(r-t)/2)` is absolutely integrable over
`N_m(F) \ GL_m(𝔸)`, uniformly over standard characters and vectors. -/
def WhittakerGaugeIntegrable {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space) (s : ℂ), C < s.re →
      Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) =>
          cuspWhittaker F T ψ v (pad F (Nat.le_of_lt (Nat.succ_lt_succ h)) q.out) *
            cuspFunction F T' v' q.out *
            detPower F (t + 1) q.out (s - ((r - t : ℕ) : ℂ) / 2))
        (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)))

/-- Dual gauge integrability (Cogdell 2004, p.207): for `Re s` beyond a bound depending only on
the realizations, `h ↦ (∫_x |W̃(rect(h, x) w')| dx) |φ̃'(h)| |det h|^(Re s-(r-t)/2)` is
integrable over `N_m(F) \ GL_m(𝔸)`, uniformly over standard characters and vectors. -/
def DualWhittakerGaugeIntegrable {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ (ψ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F ψ →
    ∀ (v : T.Space) (v' : T'.Space) (s : ℂ), C < s.re →
      Integrable (fun q : LeftCosetSpace (unipotentRationalImage F (t + 1)) =>
          (∫ x, ‖translateFunction F (r + 1) (unfoldingWeyl F h)
              (dualFunction F (r + 1) (cuspWhittaker F T ψ v)) (rectangularPoint F h q.out x)‖
            ∂rectangleMeasure F (r - (t + 1)) (t + 1)) *
          ‖dualFunction F (t + 1) (cuspFunction F T' v') q.out‖ *
          ‖detPower F (t + 1) q.out (s - ((r - t : ℕ) : ℂ) / 2)‖)
        (LeftCosetSpace.haarQuotientMeasure (unipotentRationalImage F (t + 1))
          (isDiscrete_unipotentRationalImage F (t + 1)))

/-- The four retained premises for one pair of cuspidal realizations. -/
def UnequalUnfoldingPremises {r t : ℕ} (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t) : Prop :=
  ProjectionWhittakerExpansion F h T ∧ DualProjectionWhittakerExpansion F h T ∧
    WhittakerGaugeIntegrable F h T T' ∧ DualWhittakerGaugeIntegrable F h T T'

/-- The conditional reduction: the four premises for every actual positive unequal-rank
cuspidal pair imply `UnequalUnfoldingStatement`. -/
def UnequalUnfoldingReductionStatement : Prop :=
  (∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r t : ℕ) (h : t < r)
    (T : Automorphic.CuspidalOperatorRealization F r)
    (T' : Automorphic.CuspidalOperatorRealization F t),
    UnequalUnfoldingPremises F h T T') →
  UnequalUnfoldingStatement.{u}

omit [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] in
/-- Proof of the conditional reduction. -/
theorem unequalUnfoldingReduction : UnequalUnfoldingReductionStatement.{u} := by
  intro hP F _ _ _ r t h T T'
  obtain ⟨hE, hE', ⟨C₁, hC₁, hG⟩, ⟨C₂, hC₂, hG'⟩⟩ := hP F r t h T T'
  refine ⟨max C₁ C₂, le_max_of_le_left hC₁, fun ψ hψ v v' => ?_⟩
  refine ⟨fun s hs => ?_, fun s hs => ?_⟩
  · exact ordinary_unfolding F h T T' hE ψ hψ v v' s
      (hG ψ hψ v v' s (lt_of_le_of_lt (le_max_left _ _) hs))
  · have hs' : C₂ < (1 - s).re := by
      rw [Complex.sub_re, Complex.one_re]
      linarith [le_max_right C₁ C₂]
    exact dual_unfolding F h T T' hE' ψ hψ v v' (1 - s) (hG' ψ hψ v v' (1 - s) hs')

end Langlands.Global.RankinSelbergGlobal
