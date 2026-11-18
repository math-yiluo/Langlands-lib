import Langlands.Global.RankinSelberg.ArchimedeanWhittakerRegularity
import Langlands.Global.RankinSelberg.RealPlaceWhittakerDerivative
import Langlands.Global.RankinSelberg.RealPlaceDeterminantGrowth

/-! # Smoothness and polynomial growth of actual real-place Whittaker restrictions -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical TensorProduct Manifold ContDiff Matrix.Norms.Operator CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceRestriction

open Langlands.Global.ArchimedeanGL Langlands.Automorphic
open ArchimedeanWhittakerRegularity

attribute [local instance 100] LieRing.ofAssociativeRing

local instance analyticSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance analyticSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

section Coordinates

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}

/-- Insert a matrix at one real place, with identity matrices elsewhere. -/
def realPlaceMatrix (w : RP) (A : Matrix (Fin n) (Fin n) ℝ) :
    ArchimedeanMatrix F n :=
  placeMatrixHom F n (Pi.mulSingle w A, 1)

/-- The linear part of real-place matrix insertion. -/
def realDirection (w : RP) :
    Matrix (Fin n) (Fin n) ℝ →L[ℝ] ArchimedeanMatrix F n :=
  LinearMap.toContinuousLinearMap
    ((realLieAlgebraToMatrix F n).toLinearMap ∘ₗ (realPlaceLieInclusion F n w).toLinearMap)

omit [NumberField F] in
theorem realDirection_apply (w : RP) (B : Matrix (Fin n) (Fin n) ℝ) :
    realDirection w B = placeMatrixHom F n (Pi.single w B, 0) := by
  have h : realDirection w B = placeMatrixHom F n
      (@Pi.single _ (fun _ => Matrix (Fin n) (Fin n) ℝ) _
        (fun a b => Classical.propDecidable (a = b)) w B, 0) := rfl
  rw [h]
  congr
  exact Subsingleton.elim _ _

omit [NumberField F] in
theorem realPlaceMatrix_eq_add (w : RP) (A : Matrix (Fin n) (Fin n) ℝ) :
    realPlaceMatrix w A = realPlaceMatrix w 0 + realDirection w A := by
  rw [realDirection_apply]
  refine funext fun i => funext fun j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · show (Pi.mulSingle w A : RP → Matrix (Fin n) (Fin n) ℝ) v i j =
      (Pi.mulSingle w (0 : Matrix (Fin n) (Fin n) ℝ) : RP → Matrix (Fin n) (Fin n) ℝ) v i j +
        (Pi.single w A : RP → Matrix (Fin n) (Fin n) ℝ) v i j
    by_cases h : v = w
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same, Pi.single_eq_same, Matrix.zero_apply,
        zero_add]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Pi.single_eq_of_ne h,
        Matrix.zero_apply, add_zero]
  · show (1 : Matrix (Fin n) (Fin n) ℂ) i j = (1 : Matrix (Fin n) (Fin n) ℂ) i j + 0
    exact (add_zero _).symm

theorem contDiff_realPlaceMatrix (w : RP) :
    ContDiff ℝ ∞ (realPlaceMatrix w : Matrix (Fin n) (Fin n) ℝ → ArchimedeanMatrix F n) := by
  have h : (realPlaceMatrix w : Matrix (Fin n) (Fin n) ℝ → ArchimedeanMatrix F n) =
      fun A => realPlaceMatrix w 0 + realDirection w A :=
    funext fun A => realPlaceMatrix_eq_add w A
  rw [h]
  exact contDiff_const.add (realDirection w).contDiff

omit [NumberField F] in
theorem realPlaceGL_val (w : RP) (g : Langlands.GeneralLinear n ℝ) :
    ((realPlaceGL F n w g : ArchimedeanGL F n) : ArchimedeanMatrix F n) =
      realPlaceMatrix w (g : Matrix (Fin n) (Fin n) ℝ) := by
  refine funext fun i => funext fun j => Prod.ext (funext fun v => ?_) (funext fun v => ?_)
  · refine (realPlaceGL_entry F n w v g i j).trans ?_
    show _ = (Pi.mulSingle w (g : Matrix (Fin n) (Fin n) ℝ) : RP →
      Matrix (Fin n) (Fin n) ℝ) v i j
    by_cases h : v = w
    · subst h
      rw [Pi.mulSingle_eq_same, Pi.mulSingle_eq_same]
    · rw [Pi.mulSingle_eq_of_ne h, Pi.mulSingle_eq_of_ne h, Units.val_one]
  · exact realPlaceGL_entry_snd F n w g i j v

omit [NumberField F] in
theorem isUnit_realPlaceMatrix (w : RP) {M : Matrix (Fin n) (Fin n) ℝ}
    (hM : IsUnit M) : IsUnit (realPlaceMatrix w M : ArchimedeanMatrix F n) := by
  obtain ⟨g, rfl⟩ := hM
  rw [← realPlaceGL_val]
  exact (realPlaceGL F n w g).isUnit

theorem realPlacePoint_mul_finitePoint (w : RP) (g : Langlands.GeneralLinear n ℝ)
    (b : FiniteAdelicGL F n) :
    realPlacePoint F n w g * finitePoint F n b =
      adelicPoint F n (realPlaceGL F n w g) b := by
  rw [realPlacePoint, finitePoint, mul_adelicPoint, archPart_adelicPoint, finPart_adelicPoint,
    mul_one, one_mul]

end Coordinates

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r)

theorem cuspWhittaker_realPlace (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space) (g : Langlands.GeneralLinear (r + 1) ℝ) :
    cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) =
      archWhittakerExt T χ x b (realPlaceMatrix w (g : Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ)) :=
  (congrArg (cuspWhittaker F T χ x) (realPlacePoint_mul_finitePoint w g b)).trans
    ((archWhittakerExt_units T χ hχ x b _).symm.trans
      (congrArg (archWhittakerExt T χ x b) (realPlaceGL_val w g)))

theorem contMDiff_cuspWhittaker_realPlace (χ : AddChar (Adeles F) ℂ)
    (hχ : IsStandardAdditiveCharacter F χ) (w : {v : InfinitePlace F // v.IsReal})
    (b : FiniteAdelicGL F (r + 1)) (x : T.Space) :
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : Langlands.GeneralLinear (r + 1) ℝ =>
        cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)) :=
  Archimedean.contMDiff_of_contDiffOn
    ((contDiffOn_archWhittakerExt T χ hχ x b).comp (contDiff_realPlaceMatrix w).contDiffOn
      fun _ hM => isUnit_realPlaceMatrix w hM)
    (cuspWhittaker_realPlace T χ hχ w b x)

/-- One polynomial exponent works for every vector and every standard character of the
fixed realization on the fixed real-place slice. -/
theorem exists_uniform_norm_cuspWhittaker_realPlace_le
    (w : {v : InfinitePlace F // v.IsReal}) (b : FiniteAdelicGL F (r + 1)) :
    ∃ N : ℕ, ∀ χ : AddChar (Adeles F) ℂ, IsStandardAdditiveCharacter F χ → ∀ x : T.Space,
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear (r + 1) ℝ,
        ‖cuspWhittaker F T χ x (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b)‖ ≤
          C * realMatrixHeight g ^ N := by
  obtain ⟨β, hβ⟩ := exists_norm_cuspWhittaker_le T
  obtain ⟨D, N, hD0, hD⟩ := exists_detNorm_rpow_le_realMatrixHeight F (r + 1)
    (Nat.succ_pos r) w b β
  refine ⟨N, fun χ hχ x => ?_⟩
  obtain ⟨C, hC0, hC⟩ := hβ χ hχ x
  refine ⟨C * D, mul_nonneg hC0 hD0, fun g => ?_⟩
  calc
    _ ≤ C * detNorm F (r + 1)
        (realPlacePoint F (r + 1) w g * finitePoint F (r + 1) b) ^ β := hC _
    _ ≤ C * (D * realMatrixHeight g ^ N) := mul_le_mul_of_nonneg_left (hD g) hC0
    _ = _ := (mul_assoc _ _ _).symm

end Analytic
end RealPlaceRestriction

theorem realPlaceWhittakerSmoothGrowth : RealPlaceWhittakerSmoothGrowthStatement.{u} := by
  intro F _ _ _ χ hχ r T w b x
  refine ⟨RealPlaceRestriction.contMDiff_cuspWhittaker_realPlace T χ hχ w b x, ?_⟩
  obtain ⟨N, hN⟩ := RealPlaceRestriction.exists_uniform_norm_cuspWhittaker_realPlace_le T w b
  obtain ⟨C, -, hC⟩ := hN χ hχ x
  exact ⟨C, N, hC⟩

theorem realPlaceWhittakerAnalytic : RealPlaceWhittakerAnalyticStatement.{u} :=
  realPlaceWhittakerAnalytic_of_smoothGrowth realPlaceWhittakerSmoothGrowth

theorem realPlaceWhittakerModel : RealPlaceWhittakerModelStatement.{u} :=
  realPlaceWhittakerModelReduction
    (realPlaceWhittakerIntertwinerReduction realPlaceWhittakerAnalytic)

/-- The two local analytic packages and the actual contragredient denominator comparison
imply the full real-place functional equation. -/
def RealPlaceFunctionalEquationLocalReductionStatement : Prop :=
  RealLocalUnequalJacquetStatement →
    RealLocalPositiveEqualJacquetStatement → RealPlaceContragredientPairLStatement.{u} →
    RealPlaceFunctionalEquationStatement.{u}

theorem realPlaceFunctionalEquationLocalReduction :
    RealPlaceFunctionalEquationLocalReductionStatement.{u} :=
  fun hU hE hD => realPlaceFunctionalEquationSmoothGrowthReduction hU hE
    realPlaceWhittakerSmoothGrowth hD

end Langlands.Global.RankinSelbergGlobal
