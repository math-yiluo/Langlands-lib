import Langlands.Global.RankinSelberg.WhittakerCurveDerivative
import Langlands.Global.RankinSelberg.RealPlaceWhittakerBridge
import Langlands.Representation.Archimedean.RealStandardModuleFourier

/-! # The real-place Lie derivative of a smooth actual Whittaker restriction -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator CategoryTheory.MonObj
open Langlands.LocalFactor.Archimedean
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceRestriction

open Langlands.Global.ArchimedeanGL
open Langlands.Automorphic

attribute [local instance 100] LieRing.ofAssociativeRing

local instance derivativeSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance derivativeSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
local instance derivativeRationalAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance derivativeContinuousAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance derivativeSmoothAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance derivativeFormsAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance derivativeStableAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ} :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance derivativeSpaceAddCommGroup {F : Type u} [Field F] [NumberField F] {n : ℕ}
    (S : OperatorRealization F n) : AddCommGroup S.Space := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}
local notation "RM" => Matrix (Fin n) (Fin n) ℝ
local notation "CM" => Matrix (Fin n) (Fin n) ℂ

theorem realProjection_oneParameter (v : RP) (X : RealLieAlgebra F n) (s : ℝ) :
    (realPlaceScalarProjection F v).mapMatrix (oneParameter F n X s).val =
      NormedSpace.exp (s • realPlaceLieProjection F n v X) := by
  let P : ArchimedeanMatrix F n →ₐ[ℝ] RM := (realPlaceScalarProjection F v).mapMatrix
  rw [oneParameter_val]
  exact (NormedSpace.map_exp P P.toLinearMap.continuous_of_finiteDimensional _).trans
    (congrArg NormedSpace.exp (P.toLinearMap.map_smul s (realLieAlgebraToMatrix F n X)))

theorem complexProjection_oneParameter (v : CP) (X : RealLieAlgebra F n) (s : ℝ) :
    (complexPlaceScalarProjection F v).mapMatrix (oneParameter F n X s).val =
      NormedSpace.exp (s • complexPlaceLieProjection F n v X) := by
  let P : ArchimedeanMatrix F n →ₐ[ℝ] CM := (complexPlaceScalarProjection F v).mapMatrix
  rw [oneParameter_val]
  exact (NormedSpace.map_exp P P.toLinearMap.continuous_of_finiteDimensional _).trans
    (congrArg NormedSpace.exp (P.toLinearMap.map_smul s (realLieAlgebraToMatrix F n X)))

/-- Exponentiation of a real-place Lie direction inserts the local exponential at that place. -/
theorem oneParameter_realInclusion (w : RP) (X : RM) (s : ℝ) :
    oneParameter F n (realPlaceLieInclusion F n w X) s =
      realPlaceGL F n w (Archimedean.matrixExpUnit n (s • X)) := by
  apply Units.ext
  funext i j
  refine Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · have h := realProjection_oneParameter F n v (realPlaceLieInclusion F n w X) s
    rw [realProjection_realInclusion] at h
    by_cases hv : v = w
    · subst v
      simp only [Pi.single_eq_same] at h
      exact (congrArg (fun A : RM => A i j) h).trans (by
        rw [realPlaceGL_entry]
        simp only [Pi.mulSingle_eq_same]
        rfl)
    · simp only [Pi.single_eq_of_ne hv, smul_zero, NormedSpace.exp_zero] at h
      exact (congrArg (fun A : RM => A i j) h).trans (by
        rw [realPlaceGL_entry]
        simp only [Pi.mulSingle_eq_of_ne hv]
        rfl)
  · have h := complexProjection_oneParameter F n v (realPlaceLieInclusion F n w X) s
    rw [complexProjection_realInclusion, smul_zero, NormedSpace.exp_zero] at h
    exact (congrArg (fun A : CM => A i j) h).trans
      (realPlaceGL_entry_snd F n w (Archimedean.matrixExpUnit n (s • X)) i j v).symm

theorem adelicOneParameter_realInclusion (w : RP) (X : RM) (s : ℝ) :
    WhittakerCurve.adelicOneParameter F n (realPlaceLieInclusion F n w X) s =
      realPlacePoint F n w (Archimedean.matrixExpUnit n (s • X)) := by
  simp only [WhittakerCurve.adelicOneParameter, infiniteOneParameter, oneParameter_realInclusion]
  rfl

variable {n}

set_option backward.isDefEq.respectTransparency false in
theorem lieOperator_realInclusion (S : OperatorRealization F n) (w : RP) (X : RM) (x : S.Space) :
    S.lieOperator (realPlaceLieInclusion F n w X) x =
      S.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x := by
  change S.envelopingAction (envelopingGenerator F n
      ((1 : ℂ) ⊗ₜ[ℝ] realPlaceLieInclusion F n w X)) x =
    S.envelopingAction (envelopingGenerator F n
      (realPlaceComplexLieInclusion F n w ((1 : ℂ) ⊗ₜ[ℝ] X))) x
  exact congrArg (fun Y : ComplexLieAlgebra F n =>
    S.envelopingAction (envelopingGenerator F n Y) x)
      (realPlaceComplexLieInclusion_tmul F n w 1 X).symm

variable [CompactSpace (AdeleQuotient F)]

set_option backward.isDefEq.respectTransparency false in
/-- For a smooth actual restriction the right derivative is the coefficient of the genuine
real-place Lie action. The differentiation of the integral itself has already been proved. -/
theorem rightDerivative_eq_restriction {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (hχ : IsStandardAdditiveCharacter F χ)
    (w : RP) (b : FiniteAdelicGL F (r + 1)) (x : T.Space)
    (hsm : ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ x
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)))
    (X : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ) :
    (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ
      (T.realization.realPlaceLieAction w ((1 : ℂ) ⊗ₜ[ℝ] X) x)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) =
      Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
        (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ x
          (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) := by
  funext g
  have hd := WhittakerCurve.cuspWhittaker_hasDerivAt F T χ hχ
    (realPlaceLieInclusion F (r + 1) w X) x
    (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) 0
  have hp : ∀ s : ℝ,
      realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b *
        WhittakerCurve.adelicOneParameter F (r + 1)
          (realPlaceLieInclusion F (r + 1) w X) s =
      realPlacePoint F (r + 1) w (g * Archimedean.matrixExpUnit (r + 1) (s • X)) *
        finitePoint F (r + 1) b := by
    intro s
    rw [adelicOneParameter_realInclusion, realPlacePoint_mul, mul_assoc,
      (realPlacePoint_finitePoint_commute F (r + 1) w
        (Archimedean.matrixExpUnit (r + 1) (s • X)) b).eq.symm, ← mul_assoc]
  simp only [hp, lieOperator_realInclusion, zero_smul, Archimedean.matrixExpUnit_zero,
    mul_one] at hd
  exact hd.unique (Archimedean.hasDerivAt_mul_matrixExpUnit_smul (hsm.of_le (by simp)) g X)

end RealPlaceRestriction

set_option backward.isDefEq.respectTransparency false in
/-- The remaining regularity assertions for actual real-place Whittaker restrictions:
smoothness and polynomial growth. Lie compatibility is proved from smoothness. -/
def RealPlaceWhittakerSmoothGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F χ →
  ∀ (r : ℕ) (T : Automorphic.CuspidalOperatorRealization F r)
    (w : {v : InfinitePlace F // v.IsReal}) (b : FiniteAdelicGL F (r + 1)) (x : T.Space),
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear (r + 1) ℝ => cuspWhittaker F T χ x
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) ∧
    ∃ (C : ℝ) (N : ℕ), ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
      ‖cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)‖ ≤
        C * realMatrixHeight g ^ N

theorem realPlaceWhittakerAnalytic_of_smoothGrowth
    (hSG : RealPlaceWhittakerSmoothGrowthStatement.{u}) :
    RealPlaceWhittakerAnalyticStatement.{u} := by
  intro F _ _ _ χ hχ r T w b x
  have h := hSG F χ hχ r T w b x
  exact ⟨h.1, h.2, fun X =>
    RealPlaceRestriction.rightDerivative_eq_restriction F T χ hχ w b x h.1 X⟩

theorem realPlaceWhittakerSmoothGrowth_of_analytic
    (hA : RealPlaceWhittakerAnalyticStatement.{u}) :
    RealPlaceWhittakerSmoothGrowthStatement.{u} := by
  intro F _ _ _ χ hχ r T w b x
  have h := hA F χ hχ r T w b x
  exact ⟨h.1, h.2.1⟩

/-- Two local analytic equations, actual coefficient smoothness and growth, and actual
contragredient pair-factor equality imply the exact full real-place target. -/
def RealPlaceFunctionalEquationSmoothGrowthReductionStatement : Prop :=
  RealLocalUnequalJacquetStatement →
    RealLocalPositiveEqualJacquetStatement → RealPlaceWhittakerSmoothGrowthStatement.{u} →
    RealPlaceContragredientPairLStatement.{u} →
    RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceFunctionalEquationSmoothGrowthReduction :
    RealPlaceFunctionalEquationSmoothGrowthReductionStatement.{u} :=
  fun hU hE hSG hD => realPlaceFunctionalEquationAnalyticReduction hU hE
    (realPlaceWhittakerAnalytic_of_smoothGrowth hSG) hD

end Langlands.Global.RankinSelbergGlobal
