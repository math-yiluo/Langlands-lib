import Langlands.Global.RankinSelberg.ComplexPlaceWhittakerAnalyticProof

/-! # Complex-place Whittaker restrictions with other infinite arguments frozen -/

noncomputable section

open NumberField
open scoped Classical CategoryTheory.MonObj TensorProduct Manifold ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

universe u

namespace Langlands.Global.RankinSelbergGlobal

open Automorphic LocalFactor.Archimedean
open ArchimedeanWhittakerRegularity ComplexPlaceAnalytic

local instance frozenAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance frozenSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

local notation "CP" F => {w : InfinitePlace F // InfinitePlace.IsComplex w}
local notation "GLC[" r "]" => GeneralLinear (r + 1) ℂ
local notation "Mat" r => Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ

section Analytic

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r : ℕ}
  (T : CuspidalOperatorRealization F r) (χ : AddChar (Adeles F) ℂ)
  (hχ : IsStandardAdditiveCharacter F χ) (w : CP F) (q : ArchimedeanGL F (r + 1))

private def frozenMatrix (M : Mat r) : ArchimedeanMatrix F (r + 1) :=
  (q : ArchimedeanMatrix F (r + 1)) * complexPlaceMatrix w M

omit [NumberField F] [CompactSpace (AdeleQuotient F)] in
private theorem frozenMatrix_unit (g : GLC[r]) :
    frozenMatrix w q (g : Mat r) =
      ((q * complexPlaceGL F (r + 1) w g : ArchimedeanGL F (r + 1)) :
        ArchimedeanMatrix F (r + 1)) := by
  rw [frozenMatrix, ← complexPlaceGL_val w g, Units.val_mul]

include hχ in
private theorem frozenValue (x : T.Space) (g : GLC[r]) :
    cuspWhittaker F T χ x (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1) =
      archWhittakerExt T χ x 1 (frozenMatrix w q (g : Mat r)) := by
  rw [frozenMatrix_unit, archWhittakerExt_units T χ hχ]
  rfl

include hχ in
private theorem frozenSmoothValue (x : T.Space) :
    ContMDiff (Archimedean.matrixModel ℂ (r + 1)) 𝓘(ℝ, ℂ) ∞
      (fun g : GLC[r] => cuspWhittaker F T χ x
        (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)) := by
  apply Archimedean.contMDiff_of_contDiffOn
    (ψ := fun M => archWhittakerExt T χ x 1 (frozenMatrix w q M))
  · apply (contDiffOn_archWhittakerExt T χ hχ x 1).comp
    · exact (contDiff_const.mul (contDiff_complexPlaceMatrix w)).contDiffOn
    · intro M hM
      exact q.isUnit.mul (isUnit_complexPlaceMatrix w hM)
  · exact frozenValue T χ hχ w q x

include hχ in
private theorem frozenGrowth (x : T.Space) :
    ∃ (C : ℝ) (N : ℕ), ∀ g : GLC[r],
      ‖cuspWhittaker F T χ x (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)‖ ≤
      C * complexMatrixHeight g ^ N := by
  obtain ⟨β, hβ⟩ := exists_norm_cuspWhittaker_le T
  obtain ⟨C, hC₀, hC⟩ := hβ χ hχ x
  obtain ⟨D, N, _, hD⟩ := exists_norm_det_rpow_le_complexMatrixHeight (Nat.succ_pos r) (2 * β)
  let p := adelicPoint F (r + 1) q 1
  have hp : 0 ≤ detNorm F (r + 1) p ^ β := Real.rpow_nonneg (Unfolding.detNorm_pos F (r + 1) p).le _
  refine ⟨C * detNorm F (r + 1) p ^ β * D, N, fun g => ?_⟩
  have hmul : p * complexPlacePoint F (r + 1) w g =
      adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1 := by
    dsimp only [p]
    rw [complexPlacePoint, mul_adelicPoint, archPart_adelicPoint, finPart_adelicPoint, one_mul]
  rw [← hmul]
  refine (hC _).trans ?_
  rw [Unfolding.detNorm_mul, detNorm_complexPlacePoint,
    Real.mul_rpow (Unfolding.detNorm_pos F (r + 1) p).le (by positivity),
    ← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
  rw [Nat.cast_ofNat, ← mul_assoc, mul_assoc (C * _) D]
  exact mul_le_mul_of_nonneg_left (hD g) (mul_nonneg hC₀ hp)

set_option maxHeartbeats 5000000 in
include hχ in
private theorem frozenDerivative (x : T.Space) (X : Mat r) :
    (fun g : GLC[r] => cuspWhittaker F T χ (T.realization.complexPlaceLieAction w (1 ⊗ₜ[ℝ] X) x)
        (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)) =
      Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X
        (fun g : GLC[r] => cuspWhittaker F T χ x
          (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)) := by
  funext g
  let m : Mat r := g
  let f := fun g : GLC[r] => cuspWhittaker F T χ x
    (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)
  let A := archWhittakerExt T χ x 1
  have heq : Archimedean.unitsExtension f =ᶠ[𝓝 m] fun M => A (frozenMatrix w q M) := by
    filter_upwards [Units.isOpen.mem_nhds g.isUnit] with M hM
    have hM' : IsUnit M := hM
    rw [← hM'.unit_spec, Archimedean.unitsExtension_val]
    exact frozenValue T χ hχ w q x hM'.unit
  have hderiv := (hasFDerivAt_complexPlaceMatrix w m).const_mul (q : ArchimedeanMatrix F (r + 1))
  let s := q * complexPlaceGL F (r + 1) w g
  have hA : HasFDerivAt A (fderiv ℝ A (frozenMatrix w q m)) (frozenMatrix w q m) :=
    (frozenMatrix_unit w q g) ▸
      (hasFDerivAt_archWhittakerExt T χ hχ x 1 s).differentiableAt.hasFDerivAt
  have hc := (hA.comp m hderiv).fderiv
  change fderiv ℝ (fun M => A (frozenMatrix w q M)) m = _ at hc
  change _ = Archimedean.rightDerivative (Archimedean.matrixModel ℂ (r + 1)) X f g
  rw [Archimedean.rightDerivative_eq_fderiv (frozenSmoothValue T χ hχ w q x) X g,
    heq.fderiv_eq (𝕜 := ℝ), hc, ContinuousLinearMap.comp_apply]
  change _ = fderiv ℝ A (frozenMatrix w q m)
    ((q : ArchimedeanMatrix F (r + 1)) * complexDirection w (m * X))
  have hdir : (s : ArchimedeanMatrix F (r + 1)) * complexDirection w X =
      (q : ArchimedeanMatrix F (r + 1)) * complexDirection w (m * X) := by
    dsimp only [s, m]
    rw [Units.val_mul, mul_assoc, complexPlaceGL_val, complexPlaceMatrix_mul_complexDirection]
  rw [← hdir, show frozenMatrix w q m = (s : ArchimedeanMatrix F (r + 1))
    from frozenMatrix_unit w q g]
  exact (congrArg (fun y => cuspWhittaker F T χ y _) (complexPlaceLieAction_eq_lieDeriv T w X x)).trans
    ((frozenValue T χ hχ w q (lieDeriv T (complexDirection w X) x) g).trans
      ((congrArg (archWhittakerExt T χ _ 1) (frozenMatrix_unit w q g)).trans
        (fderiv_archWhittakerExt_mul T χ hχ x 1 s (complexDirection w X)).symm))

end Analytic

/-- When the frozen archimedean argument commutes with the subgroup at a complex place, restricting
an actual place map at that argument gives an exact local Whittaker intertwiner. -/
def ComplexPlaceFrozenWhittakerStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]
    (χ : AddChar (Adeles F) ℂ), IsStandardAdditiveCharacter F χ →
  ∀ (r : ℕ) (T : CuspidalOperatorRealization F r) (w : CP F) (c : ℂˣ),
    (∀ y : InfinitePlace.Completion w.1,
      χ (((Pi.single w.1 y : InfiniteAdeles F), (0 : FiniteAdeles F)) : Adeles F) =
        ((complexScaledCharacter c
          (InfinitePlace.Completion.ringEquivComplexOfIsComplex w.2 y) : Circle) : ℂ)) →
  ∀ (q : ArchimedeanGL F (r + 1)), (∀ g : GLC[r], Commute (complexPlaceGL F (r + 1) w g) q) →
  ∀ (d : List ComplexCharacterData) (A : complexStandardKFinite (r + 1) d →ₗ[ℂ] T.Space),
    T.realization.IsComplexPlaceMap w d A →
    ∃ B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (GLC[r] → ℂ),
      IsComplexWhittakerIntertwiner r d c B ∧
        ∀ f g, B f g = cuspWhittaker F T χ (A f)
          (adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1)

set_option maxHeartbeats 5000000 in
theorem complexPlaceFrozenWhittaker : ComplexPlaceFrozenWhittakerStatement.{u} := by
  intro F _ _ _ χ hχ r T w c hcomp q hcomm d A hA
  let p (g : GLC[r]) := adelicPoint F (r + 1) (q * complexPlaceGL F (r + 1) w g) 1
  let B : complexStandardKFinite (r + 1) d →ₗ[ℂ] (GLC[r] → ℂ) :=
    { toFun := fun f g => cuspWhittaker F T χ (A f) (p g)
      map_add' := fun f f' => funext fun g => by
        rw [map_add, UnramifiedWhittaker.cuspWhittaker_add F χ hχ]
        rfl
      map_smul' := fun z f => funext fun g => by
        rw [map_smul, UnramifiedWhittaker.cuspWhittaker_smul F χ]
        rfl }
  refine ⟨B, ⟨?_, fun f => frozenSmoothValue T χ hχ w q (A f),
    fun f => frozenGrowth T χ hχ w q (A f), ?_, ?_⟩, fun f g => rfl⟩
  · intro f u hu g
    have hpt : complexPlacePoint F (r + 1) w u * p g = p (u * g) := by
      dsimp only [p]
      rw [complexPlacePoint, mul_adelicPoint, archPart_adelicPoint, finPart_adelicPoint,
        one_mul, ← mul_assoc, (hcomm u).eq, mul_assoc, map_mul]
    change cuspWhittaker F T χ (A f) (p (u * g)) =
      complexWhittakerCharacter c u * cuspWhittaker F T χ (A f) (p g)
    rw [← hpt]
    exact (Unfolding.cuspWhittaker_mul_left F T χ hχ (A f)
      ⟨_, complexPlacePoint_mem_unipotentAdelic F (r + 1) w hu⟩ _).trans
        (congrArg (· * _) (genericCharacter_complexPlacePoint F χ w c hcomp hu))
  · intro k f f' hf'
    obtain ⟨hf, he⟩ := hA.1 k f
    have hAf' := (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
    let l : Matrix.unitaryGroup (Fin (r + 1)) ℂ := ⟨(k.val : Mat r), k.2⟩
    have hk : Unitary.toUnits l = k.val := Units.ext rfl
    funext g
    change cuspWhittaker F T χ (A f') (p g) = cuspWhittaker F T χ (A f) (p (g * k.val))
    change A f' = T.realization.complexPlaceCompactRepresentation w l (A f) at hAf'
    rw [hAf', cuspWhittaker_complexPlaceCompact, complexPlaceCompactInclusion_val, hk,
      ← complexPlacePoint_eq_ofInfinite]
    congr 1
    dsimp only [p]
    rw [complexPlacePoint, mul_adelicPoint, archPart_adelicPoint, finPart_adelicPoint,
      one_mul, map_mul, mul_assoc]
  · intro X f f' hf'
    obtain ⟨hf, he⟩ := hA.2 X f
    have hAf' := (congrArg A (Subtype.ext hf' : f' = ⟨_, hf⟩)).trans he
    exact (congrArg (fun x : T.Space => fun g => cuspWhittaker F T χ x (p g)) hAf').trans
      (frozenDerivative T χ hχ w q (A f) X)

end Langlands.Global.RankinSelbergGlobal
