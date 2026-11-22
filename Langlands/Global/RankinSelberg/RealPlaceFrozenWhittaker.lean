import Langlands.Global.RankinSelberg.RealPlaceWhittakerAnalyticProof
import Langlands.Global.RankinSelberg.RealUniformWhittakerModel

/-! # Real-place Whittaker restrictions with other infinite arguments frozen -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 5000000

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic LocalFactor.Archimedean
open ArchimedeanWhittakerRegularity RealPlaceRestriction RealPlaceWhittaker
open Langlands.Global.ArchimedeanGL (realPlaceLieInclusion)

local instance realFrozenAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realFrozenSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local notation "RP" F => {w : InfinitePlace F // InfinitePlace.IsReal w}
local notation "GLR[" r "]" => GeneralLinear (r + 1) ℝ
local notation "Mat" r => Matrix (Fin (r + 1)) (Fin (r + 1)) ℝ

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (χ : AddChar (Adeles F) ℂ)
  (hχ : IsStandardAdditiveCharacter F χ) (w : RP F) (q : ArchimedeanGL F (r + 1))

omit [CompactSpace (AdeleQuotient F)] in
private theorem frozenPoint_mul (g h : GLR[r]) :
    adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1 * realPlacePoint F (r + 1) w h =
      adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w (g * h)) 1 := by
  rw [realPlacePoint, ← adelicPoint_mul, mul_one, map_mul, mul_assoc]

include hχ in
private theorem frozenRealSmoothValue (x : T.Space) :
    ContMDiff (Archimedean.matrixModel ℝ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : GLR[r] => cuspWhittaker F T χ x
        (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1)) := by
  let m (M : Mat r) := (q : ArchimedeanMatrix F (r + 1)) * realPlaceMatrix w M
  apply Archimedean.contMDiff_of_contDiffOn (ψ := fun M => archWhittakerExt T χ x 1 (m M))
  · apply (contDiffOn_archWhittakerExt T χ hχ x 1).comp
    · exact (contDiff_const.mul (contDiff_realPlaceMatrix w)).contDiffOn
    · intro M hM
      exact q.isUnit.mul (isUnit_realPlaceMatrix w hM)
  · intro g
    have h : m (g : Mat r) = ((q * realPlaceGL F (r + 1) w g : ArchimedeanGL F (r + 1)) :
        ArchimedeanMatrix F (r + 1)) := by
      dsimp only [m]
      rw [← realPlaceGL_val w g, Units.val_mul]
    rw [h, archWhittakerExt_units T χ hχ]
    rfl

include hχ in
private theorem frozenRealGrowth :
    ∃ N : ℕ, ∀ x : T.Space, ∃ C : ℝ, 0 ≤ C ∧ ∀ g : GLR[r],
      ‖cuspWhittaker F T χ x (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1)‖ ≤
        C * realMatrixHeight g ^ N := by
  obtain ⟨β, hβ⟩ := exists_norm_cuspWhittaker_le T
  obtain ⟨D, N, hD₀, hD⟩ := exists_detNorm_rpow_le_realMatrixHeight F (r + 1) (Nat.succ_pos r) w 1 β
  let p := adelicPoint F (r + 1) q 1
  have hp := Real.rpow_nonneg (Unfolding.detNorm_pos F (r + 1) p).le β
  have hFin : finitePoint F (r + 1) 1 = 1 := by
    unfold finitePoint adelicPoint
    rw [map_one]
    change (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm (AdelicGL.ofInfinite F (r + 1) 1) = 1
    rw [map_one, map_one]
  simp only [hFin, mul_one] at hD
  refine ⟨N, fun x => ?_⟩
  obtain ⟨C, hC₀, hC⟩ := hβ χ hχ x
  refine ⟨C * detNorm F (r + 1) p ^ β * D, mul_nonneg (mul_nonneg hC₀ hp) hD₀, fun g => ?_⟩
  have hg : p * realPlacePoint F (r + 1) w g =
      adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1 := by
    dsimp only [p]
    rw [realPlacePoint, ← adelicPoint_mul, mul_one]
  rw [← hg]
  refine (hC _).trans ?_
  rw [Unfolding.detNorm_mul, Real.mul_rpow (Unfolding.detNorm_pos F (r + 1) p).le
    (Unfolding.detNorm_pos F (r + 1) _).le, ← mul_assoc, mul_assoc (C * _) D]
  exact mul_le_mul_of_nonneg_left (hD g) (mul_nonneg hC₀ hp)

include hχ in
private theorem frozenRealDerivative (x : T.Space) (X : Mat r) :
    (fun g : GLR[r] => cuspWhittaker F T χ (T.realization.realPlaceLieAction w (1 ⊗ₜ[ℝ] X) x)
        (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1)) =
      Archimedean.rightDerivative (Archimedean.matrixModel ℝ (r + 1)) X
        (fun g : GLR[r] => cuspWhittaker F T χ x
          (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1)) := by
  funext g
  have hd := WhittakerCurve.cuspWhittaker_hasDerivAt F T χ hχ
    (realPlaceLieInclusion F (r + 1) w X) x (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1) 0
  simp only [adelicOneParameter_realInclusion, frozenPoint_mul, lieOperator_realInclusion,
    zero_smul, Archimedean.matrixExpUnit_zero, mul_one] at hd
  exact hd.unique (Archimedean.hasDerivAt_mul_matrixExpUnit_smul
    ((frozenRealSmoothValue T χ hχ w q x).of_le (by simp)) g X)

end Analytic

/-- Freezing an archimedean argument commuting with a real place gives a uniform
local Whittaker intertwiner on the source of an actual place map. -/
def RealPlaceFrozenWhittakerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F χ →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r) (w : RP F) (c : ℝˣ),
    (∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((realScaledCharacter c
          (InfinitePlace.Completion.ringEquivRealOfIsReal w.2 y) : Circle) : ℂ)) →
  ∀ (q : ArchimedeanGL F (r + 1)), (∀ g : GLR[r], Commute (realPlaceGL F (r + 1) w g) q) →
  ∀ (d : List RealBlock) (A : realStandardKFinite (r + 1) d →ₗ[ℂ] T.Space),
    T.realization.IsRealPlaceMap w d A →
    ∃ B : realStandardKFinite (r + 1) d →ₗ[ℂ] (GLR[r] → ℂ),
      IsRealUniformWhittakerIntertwiner r d c B ∧
        ∀ f g, B f g = cuspWhittaker F T χ (A f)
          (adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1)

theorem realPlaceFrozenWhittaker : RealPlaceFrozenWhittakerStatement.{u} := by
  intro F _ _ _ χ hχ r T w c hcomp q hcomm d A hA
  let p (g : GLR[r]) := adelicPoint F (r + 1) (q * realPlaceGL F (r + 1) w g) 1
  let B : realStandardKFinite (r + 1) d →ₗ[ℂ] (GLR[r] → ℂ) :=
    { toFun := fun f g => cuspWhittaker F T χ (A f) (p g)
      map_add' := fun f f' => funext fun g => by
        rw [map_add, UnramifiedWhittaker.cuspWhittaker_add F χ hχ]
        rfl
      map_smul' := fun z f => funext fun g => by
        rw [map_smul, UnramifiedWhittaker.cuspWhittaker_smul F χ]
        rfl }
  obtain ⟨N, hN⟩ := frozenRealGrowth T χ hχ w q
  refine ⟨B, ⟨⟨?_, fun f => frozenRealSmoothValue T χ hχ w q (A f),
    fun f => ?_, ?_, ?_⟩, ⟨N, fun f => hN (A f)⟩⟩, fun f g => rfl⟩
  · intro f u hu g
    have hpt : realPlacePoint F (r + 1) w u * p g = p (u * g) := by
      dsimp only [p]
      rw [realPlacePoint, ← adelicPoint_mul, one_mul, ← mul_assoc, (hcomm u).eq, mul_assoc, map_mul]
    change cuspWhittaker F T χ (A f) (p (u * g)) =
      realWhittakerCharacter c u * cuspWhittaker F T χ (A f) (p g)
    rw [← hpt]
    exact (Unfolding.cuspWhittaker_mul_left F T χ hχ (A f)
      ⟨_, realPlacePoint_mem_unipotent F (r + 1) w ⟨u, hu⟩⟩ _).trans
        (congrArg (· * _) (genericCharacter_realPlacePoint F χ w c hcomp hu))
  · obtain ⟨C, _, hC⟩ := hN (A f)
    exact ⟨C, N, hC⟩
  · intro k f f' hf'
    obtain ⟨hf, he⟩ := hA.1 k f
    have hAf' := (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
    let l : Matrix.unitaryGroup (Fin (r + 1)) ℝ := ⟨(k.val : Mat r), k.2⟩
    have hk : Unitary.toUnits l = k.val := Units.ext rfl
    funext g
    change cuspWhittaker F T χ (A f') (p g) = cuspWhittaker F T χ (A f) (p (g * k.val))
    change A f' = T.realization.realPlaceCompactRepresentation w l (A f) at hAf'
    rw [hAf', cuspWhittaker_realPlaceCompact, ← realPlacePoint_unitary, hk]
    exact congrArg (cuspWhittaker F T χ (A f)) (frozenPoint_mul w q g k.val)
  · intro X f f' hf'
    obtain ⟨hf, he⟩ := hA.2 X f
    have hAf' := (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
    exact (congrArg (fun x : T.Space => fun g => cuspWhittaker F T χ x (p g)) hAf').trans
      (frozenRealDerivative T χ hχ w q (A f) X)

end Langlands.Global.RankinSelbergGlobal
