import Langlands.Global.RankinSelberg.EqualUnfoldingEisenstein
import Langlands.Global.RankinSelberg.EqualUnfoldingWhittaker
import Langlands.Global.RankinSelberg.EqualAnalyticFourierDominated

/-! # Cusp forms, their duals and Schwartz–Bruhat functions in the equal-rank unfolding -/

noncomputable section
universe u
open NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.EqualUnfolding

open Langlands.Global Unfolding

local instance equalCuspSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.IsAffine (Scheme F n).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance equalCuspSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    AlgebraicGeometry.Smooth (Scheme F n).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement _ _

attribute [local instance] equalSectionRowMeasurableSpace equalSectionRowBorelSpace

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)]

local instance equalCuspUnipotentLocallyCompactSpace (n : ℕ) :
    LocallyCompactSpace (unipotentAdelic F n) :=
  (isClosed_upperUnipotent_adelicPoints F n).locallyCompactSpace

section SchwartzBruhat

/-- Schwartz–Bruhat functions are measurable. -/
theorem measurable_of_mem_schwartzBruhat {n : ℕ} {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) : Measurable Φ :=
  (EqualAnalytic.schwartzBruhat_properties F n hΦ).1.measurable

/-- Fourier transforms of Schwartz–Bruhat functions are measurable. -/
theorem measurable_fourierTransform {n : ℕ} (ψ : AddChar (Adeles F) ℂ)
    (hψ : IsStandardAdditiveCharacter F ψ) {Φ : RowVector F n → ℂ}
    (hΦ : Φ ∈ schwartzBruhat F n) : Measurable (fourierTransform F n ψ Φ) :=
  (EqualAnalytic.continuous_fourierTransform F n ψ hψ
    (EqualAnalytic.schwartzBruhat_properties F n hΦ).2.1).measurable

end SchwartzBruhat

section CentralCharacter

variable {r : ℕ}

/-- A cusp function is the evaluation of its continuous automorphic form at the matrix of
the point. -/
theorem cuspFunction_eq_evaluate (T : Automorphic.CuspidalOperatorRealization F r)
    (v : T.Space) (x : Points F (r + 1)) :
    cuspFunction F T v x = Automorphic.ContinuousRationalFunctions.evaluate F (r + 1)
      (T.realization.toContinuous v) (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x) := by
  have hx := Automorphic.GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F
    (r + 1) ((Automorphic.GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous v)) x
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx.symm

/-- Cusp forms with central character `ω` transform by `ω(a)` under the scalar `a`. -/
theorem cuspFunction_scalarPoint_mul (T : Automorphic.CuspidalOperatorRealization F r)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (v : T.Space) (z : Points F 1) (x : Points F (r + 1)) :
    cuspFunction F T v (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F ω (ideleOf F z) : ℂ) * cuspFunction F T v x := by
  rw [cuspFunction_eq_evaluate, cuspFunction_eq_evaluate, map_mul]
  have h1 := adelicEquiv_scalarPoint F r z
  rw [← GeneralLinearGroupPoints.adelicHomeomorph_toMulEquiv] at h1
  have h2 : (Matrix.GeneralLinearGroup.scalar (Fin (r + 1)) (ideleOf F z) :
      AdelicGL F (r + 1)) = AdelicGL.scalar F (r + 1) (ideleOf F z) := rfl
  have h : GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) (scalarPoint F r z) =
      AdelicGL.scalar F (r + 1) (ideleOf F z) := by
    rw [← h2, ← h1]
    rfl
  refine (congrArg (fun g => Automorphic.ContinuousRationalFunctions.evaluate F (r + 1)
    (T.realization.toContinuous v) (g * GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x))
    h).trans ?_
  exact T.realization.centralCharacter_evaluate ω hω v (ideleOf F z) _

omit [CompactSpace (AdeleQuotient F)] in
/-- The twist `g ↦ w ᵗg⁻¹ w⁻¹` inverts scalars. -/
theorem dualConj_scalarPoint (z : Points F 1) :
    dualConj F (r + 1) (scalarPoint F r z) = scalarPoint F r z⁻¹ := by
  apply (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).injective
  rw [adelicEquiv_dualConj, adelicEquiv_scalarPoint, adelicEquiv_scalarPoint, ideleOf_inv]
  ext i j
  rw [dualConjGL_entry, ← map_inv]
  change (Matrix.scalar (Fin (r + 1)) (((ideleOf F z)⁻¹ : IdeleGroup (𝓞 F) F) : Adeles F) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) j.rev i.rev =
    (Matrix.scalar (Fin (r + 1)) (((ideleOf F z)⁻¹ : IdeleGroup (𝓞 F) F) : Adeles F) :
      Matrix (Fin (r + 1)) (Fin (r + 1)) (Adeles F)) i j
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Fin.rev_inj]
  rcases eq_or_ne i j with rfl | h
  · simp
  · simp [h, h.symm]

/-- Dual cusp forms transform by `ω(a)⁻¹` under the scalar `a`. -/
theorem dualCuspFunction_scalarPoint_mul (T : Automorphic.CuspidalOperatorRealization F r)
    {ω : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (v : T.Space) (z : Points F 1) (x : Points F (r + 1)) :
    dualFunction F (r + 1) (cuspFunction F T v) (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F ω (ideleOf F z) : ℂ)⁻¹ *
        dualFunction F (r + 1) (cuspFunction F T v) x := by
  rw [dualFunction_eq, dualFunction_eq, dualPoint_mul, dualConj_scalarPoint,
    cuspFunction_scalarPoint_mul F T hω, ideleOf_inv, map_inv, Units.val_inv_eq_inv_val]

omit [CompactSpace (AdeleQuotient F)] in
theorem centralIdeleCharacter_mul_val (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (a : IdeleGroup (𝓞 F) F) :
    (Automorphic.centralIdeleCharacter F (ω * ω') a : ℂ) =
      (Automorphic.centralIdeleCharacter F ω a : ℂ) *
        (Automorphic.centralIdeleCharacter F ω' a : ℂ) := by
  rw [← Units.val_mul]
  rfl

omit [CompactSpace (AdeleQuotient F)] in
theorem centralIdeleCharacter_mul_inv_val (ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ)
    (a : IdeleGroup (𝓞 F) F) :
    (Automorphic.centralIdeleCharacter F (ω * ω')⁻¹ a : ℂ) =
      (Automorphic.centralIdeleCharacter F ω a : ℂ)⁻¹ *
        (Automorphic.centralIdeleCharacter F ω' a : ℂ)⁻¹ := by
  rw [← Units.val_inv_eq_inv_val, ← Units.val_inv_eq_inv_val, ← Units.val_mul]
  change ((ω * ω') (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F) a))⁻¹.val = _
  rw [show (ω * ω') (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F) a) =
      ω (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F) a) *
        ω' (QuotientGroup.mk' (IdeleGroup.principalSubgroup (𝓞 F) F) a) from rfl, mul_inv]
  rfl

/-- The product of two cusp forms transforms by `ω ω'` under scalars. -/
theorem cuspFunction_mul_scalarPoint_mul (T T' : Automorphic.CuspidalOperatorRealization F r)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (hω' : T'.realization.HasCentralCharacter ω') (v : T.Space) (v' : T'.Space)
    (z : Points F 1) (x : Points F (r + 1)) :
    cuspFunction F T v (scalarPoint F r z * x) * cuspFunction F T' v' (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F (ω * ω') (ideleOf F z) : ℂ) *
        (cuspFunction F T v x * cuspFunction F T' v' x) := by
  rw [cuspFunction_scalarPoint_mul F T hω, cuspFunction_scalarPoint_mul F T' hω',
    centralIdeleCharacter_mul_val]
  ring

/-- The product of two dual cusp forms transforms by `(ω ω')⁻¹` under scalars. -/
theorem dualCuspFunction_mul_scalarPoint_mul
    (T T' : Automorphic.CuspidalOperatorRealization F r)
    {ω ω' : IdeleClassGroup (𝓞 F) F →ₜ* ℂˣ} (hω : T.realization.HasCentralCharacter ω)
    (hω' : T'.realization.HasCentralCharacter ω') (v : T.Space) (v' : T'.Space)
    (z : Points F 1) (x : Points F (r + 1)) :
    dualFunction F (r + 1) (cuspFunction F T v) (scalarPoint F r z * x) *
        dualFunction F (r + 1) (cuspFunction F T' v') (scalarPoint F r z * x) =
      (Automorphic.centralIdeleCharacter F (ω * ω')⁻¹ (ideleOf F z) : ℂ) *
        (dualFunction F (r + 1) (cuspFunction F T v) x *
          dualFunction F (r + 1) (cuspFunction F T' v') x) := by
  rw [dualCuspFunction_scalarPoint_mul F T hω, dualCuspFunction_scalarPoint_mul F T' hω',
    centralIdeleCharacter_mul_inv_val]
  ring

end CentralCharacter

section Whittaker

variable {r : ℕ}

/-- The `ψ⁻¹`-Whittaker function of a cusp form, written over the fundamental domain of
`N_n(F)` in `N_n(𝔸)`. -/
theorem cuspWhittaker_inv_eq_setIntegral (T' : Automorphic.CuspidalOperatorRealization F r)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (v' : T'.Space)
    (x : Points F (r + 1)) :
    cuspWhittaker F T' ψ⁻¹ v' x =
      ((AdelicSubgroupPoints.quotientMassNormalizer F (Scheme F (r + 1))
          (upperUnipotent F (r + 1))).toReal : ℂ) *
        ∫ n in unipotentFundamentalDomain F (r + 1),
          cuspFunction F T' v' ((n : Points F (r + 1)) * x) *
            genericCharacter F r ψ (fun _ => 1) n ∂Measure.haar := by
  have hψ' := isStandardAdditiveCharacter_inv F ψ hψ
  have hφ'm : Measurable (cuspFunction F T' v') := (continuous_cuspFunction F T' v').measurable
  have hW' := subgroupCharacterCoefficient_eq_setIntegral F (Scheme F (r + 1))
    (upperUnipotent F (r + 1)) (genericCharacter F r ψ⁻¹ fun _ => 1)
    (continuous_genericCharacter F r ψ⁻¹ hψ'.1 _).measurable
    (genericCharacter_rational_mul F r ψ⁻¹ hψ') (cuspFunction F T' v') hφ'm
    (fun k y => cuspFunction_rational_mul F T' v' (mem_rationalSubgroup_of_unipotent F k) y) x
  have hconj : ∀ n : unipotentAdelic F (r + 1),
      starRingEnd ℂ (genericCharacter F r ψ⁻¹ (fun _ => 1) n) =
        genericCharacter F r ψ (fun _ => 1) n := fun n => by
    rw [genericCharacter_inv F r ψ hψ.2.2.2, Complex.conj_conj]
  simp_rw [hconj] at hW'
  rw [← Complex.real_smul]
  exact hW'

end Whittaker

end Langlands.Global.RankinSelbergGlobal.EqualUnfolding
