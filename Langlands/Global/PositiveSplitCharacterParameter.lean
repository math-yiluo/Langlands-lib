import Langlands.Global.AdelicComplexParameters
import Langlands.Global.AdelicLogSection
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Mathlib.Topology.Instances.RealVectorSpace

/-! # Positive continuous characters as parabolic parameters -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj NNReal TensorProduct

set_option autoImplicit false

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints

/-- If the integral character restriction has finite-index image, every
continuous positive character of the intrinsic split subgroup is the
restriction of a complex parameter of the ambient group. -/
def PositiveSplitCharacterParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (P : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F))) (j : A.toGrp ⟶ P),
    IsSplitTorus A.toGrp → (characterRestrict j).range.FiniteIndex →
      ∀ (eta : intrinsicSubgroup F A →* ℝ≥0ˣ),
        Continuous (fun x => ((eta x : ℝ≥0) : ℝ)) →
          ∃ lam : ComplexCharacterParameter F P, ∀ x : intrinsicSubgroup F A,
            parameterPower F P lam (positivePointMap F P A j x) = (((eta x : ℝ≥0) : ℝ) : ℂ)

theorem positiveSplitCharacterParameter : PositiveSplitCharacterParameterStatement.{u} := by
  classical
  intro F _ _ P A j hA hIndex eta heta
  obtain ⟨I, hI, ⟨e⟩⟩ := hA
  let : Fintype I := Fintype.ofFinite I
  let logs := positiveLogEquiv F A I e
  let coords := dualCoordinatesContinuousEquiv F A I e
  let point := fun x : I → ℝ => logs.symm (Multiplicative.ofAdd (coords.symm x))
  have hp0 : point 0 = 1 := by
    change logs.symm (Multiplicative.ofAdd (coords.symm 0)) = 1
    rw [map_zero]
    exact map_one logs.symm
  have hpAdd (x y : I → ℝ) : point (x + y) = point x * point y := by
    change logs.symm (Multiplicative.ofAdd (coords.symm (x + y))) = _
    rw [map_add]
    exact map_mul logs.symm (Multiplicative.ofAdd (coords.symm x)) (Multiplicative.ofAdd (coords.symm y))
  have hpC : Continuous point := logs.symm.continuous.comp coords.symm.continuous
  have hpos (x : intrinsicSubgroup F A) : 0 < ((eta x : ℝ≥0) : ℝ) :=
    NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr (eta x).ne_zero)
  let logChar : (I → ℝ) →+ ℝ :=
    { toFun := fun x => Real.log ((eta (point x) : ℝ≥0) : ℝ)
      map_zero' := by rw [hp0, map_one]; simp
      map_add' := fun x y => by
        rw [hpAdd, map_mul, Units.val_mul, NNReal.coe_mul,
          Real.log_mul (hpos (point x)).ne' (hpos (point y)).ne'] }
  have hLogC : Continuous logChar := by
    apply continuous_iff_continuousAt.mpr
    intro x
    have hPre : ContinuousAt (fun y : I → ℝ => ((eta (point y) : ℝ≥0) : ℝ)) x :=
      (heta.comp hpC).continuousAt
    exact ContinuousAt.comp (f := fun y : I → ℝ => ((eta (point y) : ℝ≥0) : ℝ))
      (x := x) (Real.continuousAt_log (hpos (point x)).ne') hPre
  let L := logChar.toRealLinearMap hLogC
  let b : I → ℝ := fun i => L (Pi.single i 1)
  have hLinear (v : I → ℝ) : L v = ∑ i, v i * b i := by
    have hv : (∑ i, v i • Pi.single i (1 : ℝ)) = v := by
      funext i
      simp [Finset.sum_apply, Pi.single_apply, smul_eq_mul]
    rw [← hv] at ⊢
    conv_lhs => rw [map_sum]
    simp only [map_smul, smul_eq_mul, hv, b]
  let χ := coordinateCharacter F I A e
  have hLift (i : I) : ∃ (d : ℕ), 0 < d ∧ ∃ ψ : rationalCharacters P,
      characterRestrict j ψ = d • χ i := by
    obtain ⟨d, hd, _, hm⟩ := (characterRestrict j).range.exists_nsmul_mem_of_index_ne_zero
      hIndex.index_ne_zero (χ i)
    exact ⟨d, hd, hm⟩
  choose d hd ψ hψ using hLift
  let lam : ComplexCharacterParameter F P := ∑ i, ((b i / (d i : ℝ) : ℝ) : ℂ) ⊗ₜ[ℤ] ψ i
  refine ⟨lam, fun x => ?_⟩
  let v : I → ℝ := coords (characterLog F A.toGrp x.val)
  have hpt : point v = x := by
    change logs.symm (Multiplicative.ofAdd (coords.symm (coords (characterLog F A.toGrp x.val)))) = x
    rw [coords.symm_apply_apply]
    exact logs.symm_apply_apply x
  have hv (i : I) : v i = characterLog F A.toGrp x.val (χ i) := rfl
  have hpLog (i : I) : characterLog F P (positivePointMap F P A j x) (ψ i) = (d i : ℝ) * v i := by
    rw [positivePointMap_apply, characterLog_map]
    let logValue : rationalCharacters A.toGrp →+ ℝ := characterLog F A.toGrp x.val
    change logValue (characterRestrict j (ψ i)) = _
    rw [hψ, logValue.map_nsmul, nsmul_eq_mul]
    rfl
  have hPair : complexParameterPairing F P lam (characterLog F P (positivePointMap F P A j x)) =
      (Real.log ((eta x : ℝ≥0) : ℝ) : ℂ) := by
    have hLog : Real.log ((eta x : ℝ≥0) : ℝ) = ∑ i, v i * b i := by
      have h := hLinear v
      change Real.log ((eta (point v) : ℝ≥0) : ℝ) = _ at h
      rwa [hpt] at h
    rw [hLog, Complex.ofReal_sum]
    unfold lam
    simp only [map_sum, LinearMap.sum_apply, complexParameterPairing_tmul, hpLog, ← Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    congr 1
    rw [← mul_assoc, div_mul_cancel₀ _ (by exact_mod_cast (hd i).ne'), mul_comm]
  unfold parameterPower
  rw [hPair, ← Complex.ofReal_exp, Real.exp_log (hpos x)]

end Langlands.Global.PositiveRealTorus
