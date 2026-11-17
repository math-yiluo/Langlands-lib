import Langlands.Global.RankinSelberg.RealMatrixHeightBounds
import Langlands.Global.RankinSelberg.ArchimedeanPlaces
import Langlands.Global.RankinSelberg.UnfoldingGL

/-! # The actual adelic determinant norm on a real-place slice -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal
namespace RealPlaceRestriction

open Langlands.Global.ArchimedeanGL

local instance growthSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance growthSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

omit [NumberField F] in
theorem realProjection_det_realPlaceGL (w v : RP) (g : Langlands.GeneralLinear n ℝ) :
    realPlaceScalarProjection F v (realPlaceGL F n w g).val.det =
      ((Pi.mulSingle w g : RP → Langlands.GeneralLinear n ℝ) v).val.det := by
  rw [AlgHom.map_det]
  congr 1

omit [NumberField F] in
theorem complexProjection_det_realPlaceGL (w : RP) (v : CP)
    (g : Langlands.GeneralLinear n ℝ) :
    complexPlaceScalarProjection F v (realPlaceGL F n w g).val.det = 1 := by
  rw [AlgHom.map_det]
  have he : (complexPlaceScalarProjection F v).mapMatrix (realPlaceGL F n w g).val =
      (1 : Matrix (Fin n) (Fin n) ℂ) := by
    funext i j
    rfl
  rw [he, Matrix.det_one]

theorem detNorm_realPlacePoint (w : RP) (g : Langlands.GeneralLinear n ℝ) :
    detNorm F n (realPlacePoint F n w g) = |g.val.det| := by
  let q : (InfiniteAdeles F)ˣ :=
    Matrix.GeneralLinearGroup.det ((archimedeanGLCoordinates F n).symm (realPlaceGL F n w g))
  have hq : q.val = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
      (realPlaceGL F n w g).val.det := by
    exact ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_det _).symm
  have hnorm (v : InfinitePlace F) :
      ‖q.val v‖ = if v = w.1 then |g.val.det| else 1 := by
    by_cases hv : v.IsReal
    · rw [hq, infiniteAdeleCoordinates_symm_real F _ v hv]
      have he : ‖(InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm
          ((realPlaceGL F n w g).val.det.1 ⟨v, hv⟩)‖ =
          ‖(realPlaceGL F n w g).val.det.1 ⟨v, hv⟩‖ :=
        (InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm) _
      rw [he]
      change ‖realPlaceScalarProjection F ⟨v, hv⟩ (realPlaceGL F n w g).val.det‖ = _
      rw [realProjection_det_realPlaceGL]
      by_cases heq : v = w.1
      · simp only [Pi.mulSingle_eq_same, heq, ite_true, Real.norm_eq_abs]
      · have hsub : (⟨v, hv⟩ : RP) ≠ w := fun h => heq (congrArg Subtype.val h)
        simp only [Pi.mulSingle_eq_of_ne hsub, Units.val_one, Matrix.det_one,
          norm_one, heq, ite_false]
    · have hc := InfinitePlace.not_isReal_iff_isComplex.mp hv
      have hne : v ≠ w.1 := fun h => hv (h ▸ w.2)
      rw [hq, infiniteAdeleCoordinates_symm_complex F _ v hc]
      have he : ‖(InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm
          ((realPlaceGL F n w g).val.det.2 ⟨v, hc⟩)‖ =
          ‖(realPlaceGL F n w g).val.det.2 ⟨v, hc⟩‖ :=
        (InfinitePlace.Completion.isometryEquivComplexOfIsComplex hc).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hc).symm) _
      rw [he]
      change ‖complexPlaceScalarProjection F ⟨v, hc⟩ (realPlaceGL F n w g).val.det‖ = _
      rw [complexProjection_det_realPlaceGL, norm_one, ite_eq_right hne]
  have hprod : ∏ v : InfinitePlace F, ‖q.val v‖ ^ v.mult = |g.val.det| := by
    rw [Finset.prod_eq_single w.1 (fun v _ hv => ?_) (by simp)]
    · rw [hnorm, ite_eq_left rfl, w.2.mult_eq_one, pow_one]
    · rw [hnorm, ite_eq_right hv, one_pow]
  unfold detNorm
  rw [AdelicBlockDeterminantCharacter.determinantNorm_split]
  simp only [realPlacePoint, adelicPoint, MulEquiv.apply_symm_apply,
    AdelicGL.infinite_pair, AdelicGL.finite_pair, map_one, mul_one]
  exact hprod

theorem exists_detNorm_rpow_le_realMatrixHeight (hn : 0 < n) (w : RP)
    (b : FiniteAdelicGL F n) (β : ℝ) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear n ℝ,
      detNorm F n (realPlacePoint F n w g * finitePoint F n b) ^ β ≤
        C * realMatrixHeight g ^ N := by
  obtain ⟨C, N, hC, hbound⟩ := exists_det_rpow_le_realMatrixHeight hn β
  have hd := Unfolding.detNorm_pos F n (finitePoint F n b)
  refine ⟨C * detNorm F n (finitePoint F n b) ^ β, N,
    mul_nonneg hC (Real.rpow_nonneg hd.le _), fun g => ?_⟩
  rw [Unfolding.detNorm_mul, detNorm_realPlacePoint,
    Real.mul_rpow (abs_nonneg _) hd.le]
  calc
    _ ≤ (C * realMatrixHeight g ^ N) * detNorm F n (finitePoint F n b) ^ β :=
      mul_le_mul_of_nonneg_right (hbound g) (Real.rpow_nonneg hd.le _)
    _ = _ := by ring

end RealPlaceRestriction

/-- Every real power of the actual adelic determinant norm has polynomial growth on a
single real-place matrix slice, with an arbitrary fixed finite adelic component. -/
def RealPlaceDeterminantGrowthStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] (n : ℕ), 0 < n →
  ∀ (w : {v : InfinitePlace F // v.IsReal}) (b : FiniteAdelicGL F n) (β : ℝ),
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ g : Langlands.GeneralLinear n ℝ,
      detNorm F n (realPlacePoint F n w g * finitePoint F n b) ^ β ≤
        C * realMatrixHeight g ^ N

theorem realPlaceDeterminantGrowth : RealPlaceDeterminantGrowthStatement.{u} :=
  fun F _ _ n hn w b β =>
    RealPlaceRestriction.exists_detNorm_rpow_le_realMatrixHeight F n hn w b β

end Langlands.Global.RankinSelbergGlobal
