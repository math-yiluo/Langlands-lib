import Langlands.Global.RankinSelberg.RealPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.RealLocalWhittakerProperties

/-! # Uniform growth of all real-place derivatives of actual Whittaker restrictions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceRestriction

open Langlands.Automorphic RealLocalWhittaker

local instance uniformSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance uniformSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)
  (w : {v : InfinitePlace F // v.IsReal})

/-- A word of genuine real-place Lie actions, with the first direction acting last. -/
def iteratedLieAction
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) (x : T.Space) : T.Space :=
  Xs.foldr (fun X y => T.realization.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) y) x

/-- Each matrix right-derivative word is the restriction of the corresponding genuine
Lie-action word on the original cuspidal realization. -/
theorem iteratedRightDerivative_eq_restriction
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    iteratedRightDerivative r Xs
      (fun g : Langlands.GeneralLinear (r + 1) ℝ =>
        cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
      fun g : Langlands.GeneralLinear (r + 1) ℝ =>
        cuspWhittaker F T χ (iteratedLieAction T w Xs x)
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) := by
  induction Xs with
  | nil => rfl
  | cons X Xs ih =>
    change Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
      (iteratedRightDerivative r Xs _) = _
    rw [ih]
    exact (rightDerivative_eq_restriction F T χ hχ w b (iteratedLieAction T w Xs x)
      (contMDiff_cuspWhittaker_realPlace T χ hχ w b _) X).symm

theorem contMDiff_iteratedRightDerivative
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space)
    (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (iteratedRightDerivative r Xs (fun g : Langlands.GeneralLinear (r + 1) ℝ =>
        cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b))) := by
  rw [iteratedRightDerivative_eq_restriction T w χ hχ b x Xs]
  exact contMDiff_cuspWhittaker_realPlace T χ hχ w b _

/-- The exponent is chosen before the standard character, vector, and derivative word. -/
theorem exists_uniform_norm_iteratedRightDerivative_le
    (b : FiniteAdelicGL F (r + 1)) :
    ∃ N : ℕ, ∀ χ : AddChar (Adeles F) ℂ, IsStandardAdditiveCharacter F χ →
      ∀ (x : T.Space) (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
          ‖iteratedRightDerivative r Xs (fun h : Langlands.GeneralLinear (r + 1) ℝ =>
            cuspWhittaker F T χ x
              (realPlacePoint F (r + 1) w h * finitePoint F (r + 1) b)) g‖ ≤
            C * realMatrixHeight g ^ N := by
  obtain ⟨N, hN⟩ := exists_uniform_norm_cuspWhittaker_realPlace_le T w b
  refine ⟨N, fun χ hχ x Xs => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hN χ hχ (iteratedLieAction T w Xs x)
  refine ⟨C, hC0, ?_⟩
  rw [iteratedRightDerivative_eq_restriction T w χ hχ b x Xs]
  exact hC

end RealPlaceRestriction

/-- All finite real matrix right-derivative words of actual global Whittaker restrictions
admit one common polynomial exponent on each fixed real-place slice. -/
def RealPlaceWhittakerUniformGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsReal}) (b : FiniteAdelicGL F (r + 1)),
    ∃ N : ℕ, ∀ χ : AddChar (Adeles F) ℂ, IsStandardAdditiveCharacter F χ →
      ∀ (x : T.Space) (Xs : List (Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)),
        ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
          ‖RealLocalWhittaker.iteratedRightDerivative r Xs
            (fun h : Langlands.GeneralLinear (r + 1) ℝ =>
              cuspWhittaker F T χ x
                (realPlacePoint F (r + 1) w h * finitePoint F (r + 1) b)) g‖ ≤
            C * realMatrixHeight g ^ N

theorem realPlaceWhittakerUniformGrowth : RealPlaceWhittakerUniformGrowthStatement.{u} :=
  fun _ _ _ _ _ T w b =>
    RealPlaceRestriction.exists_uniform_norm_iteratedRightDerivative_le T w b

end Langlands.Global.RankinSelbergGlobal
