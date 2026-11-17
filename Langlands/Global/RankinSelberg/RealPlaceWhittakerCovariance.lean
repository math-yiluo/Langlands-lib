import Langlands.Global.RankinSelberg.RealPlaceMinusOneAction
import Langlands.Global.RankinSelberg.UnfoldingGL
import Langlands.Global.RankinSelberg.ArchimedeanIntegrals
import Langlands.Global.AdelicGLInverseTranspose
import Langlands.Global.RankinSelberg.UnfoldingDualGL

/-! # Actual real-place Whittaker covariance -/

noncomputable section
universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped Classical CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000

namespace Langlands.Global.RankinSelbergGlobal

open Langlands.Automorphic

local instance realCovarianceSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realCovarianceSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

variable (F : Type u) [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}

theorem adelicPoint_mul (n : ℕ) (g h : ArchimedeanGL F n)
    (a b : FiniteAdelicGL F n) :
    adelicPoint F n (g * h) (a * b) =
      adelicPoint F n g a * adelicPoint F n h b := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [adelicPoint, MulEquiv.apply_symm_apply, map_mul]
  apply AdelicGL.ext_infinite_finite F n
  · simp only [map_mul, AdelicGL.infinite_pair]
  · simp only [map_mul, AdelicGL.finite_pair]

theorem realPlacePoint_mul (n : ℕ) (v : RP)
    (g h : Langlands.GeneralLinear n ℝ) :
    realPlacePoint F n v (g * h) =
      realPlacePoint F n v g * realPlacePoint F n v h := by
  simpa only [realPlacePoint, map_mul, one_mul] using
    adelicPoint_mul F n (realPlaceGL F n v g) (realPlaceGL F n v h) 1 1

theorem realPlacePoint_finitePoint_commute (n : ℕ) (v : RP)
    (g : Langlands.GeneralLinear n ℝ) (a : FiniteAdelicGL F n) :
    Commute (realPlacePoint F n v g) (finitePoint F n a) := by
  change adelicPoint F n (realPlaceGL F n v g) 1 * adelicPoint F n 1 a =
    adelicPoint F n 1 a * adelicPoint F n (realPlaceGL F n v g) 1
  rw [← adelicPoint_mul, ← adelicPoint_mul]
  simp only [mul_one, one_mul]

omit [NumberField F] in
theorem realPlaceGL_unitary (n : ℕ) (v : RP)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realPlaceGL F n v (Unitary.toUnits k) =
      archimedeanGLCoordinates F n (realPlaceCompactInclusion F n v k).val := by
  change _ = archimedeanGLCoordinates F n
    (ArchimedeanCompactFactors.toInfiniteAdelicGL F n
      (ArchimedeanCompactFactors.realPlaceFactor F n v k))
  rw [ArchimedeanCompactFactors.coordinates_toInfiniteAdelicGL]
  apply Units.ext
  apply Matrix.ext
  intro i j
  apply Prod.ext
  · funext w
    change (Pi.mulSingle v (Unitary.toUnits k) : RP →
        Langlands.GeneralLinear n ℝ) w i j =
      (Pi.mulSingle v k : RP → Matrix.unitaryGroup (Fin n) ℝ) w i j
    by_cases hw : w = v
    · subst w
      simp
    · simp [hw]
  · funext w
    rfl

theorem realPlacePoint_unitary (n : ℕ) (v : RP)
    (k : Matrix.unitaryGroup (Fin n) ℝ) :
    realPlacePoint F n v (Unitary.toUnits k) =
      (GeneralLinearGroupPoints.adelicEquiv F n).symm
        (AdelicGL.ofInfinite F n (realPlaceCompactInclusion F n v k).val) := by
  apply (GeneralLinearGroupPoints.adelicEquiv F n).injective
  simp only [realPlacePoint, adelicPoint, MulEquiv.apply_symm_apply]
  apply AdelicGL.ext_infinite_finite F n
  · simp only [AdelicGL.infinite_pair, AdelicGL.infinite_ofInfinite,
      realPlaceGL_unitary]
    exact (archimedeanGLCoordinates F n).symm_apply_apply _
  · simp only [AdelicGL.finite_pair, AdelicGL.finite_ofInfinite]

theorem realPlacePoint_minusOne (n : ℕ) (v : RP) :
    realPlacePoint F n v (-1) =
      (GeneralLinearGroupPoints.adelicEquiv F n).symm
        (AdelicGL.ofInfinite F n (realPlaceCompactInclusion F n v (-1)).val) := by
  have hk : Unitary.toUnits (-1 : Matrix.unitaryGroup (Fin n) ℝ) =
      (-1 : Langlands.GeneralLinear n ℝ) := Units.ext rfl
  simpa only [hk] using realPlacePoint_unitary F n v (-1)

omit [NumberField F] in
theorem realPlaceGL_isUnitriangular (n : ℕ) (v : RP)
    (u : GeneralLinear.upperUnipotent n ℝ) :
    PrimitiveAdelicHeight.IsUnitriangular (realPlaceGL F n v u.val).val := by
  constructor
  · intro i j hij
    change j < i at hij
    apply Prod.ext
    · funext w
      change (Pi.mulSingle v u.val : RP → Langlands.GeneralLinear n ℝ) w i j = 0
      by_cases hw : w = v
      · subst w
        simpa only [Pi.mulSingle_eq_same, id_eq] using
          GeneralLinear.UpperUnipotent.entry_eq_zero u hij
      · simp only [Pi.mulSingle_eq_of_ne hw]
        change (1 : Matrix (Fin n) (Fin n) ℝ) i j = 0
        exact Matrix.one_apply_ne hij.ne'
    · funext w
      change (1 : Matrix (Fin n) (Fin n) ℂ) i j = 0
      exact Matrix.one_apply_ne hij.ne'
  · intro i
    apply Prod.ext
    · funext w
      change (Pi.mulSingle v u.val : RP → Langlands.GeneralLinear n ℝ) w i i = 1
      by_cases hw : w = v
      · subst w
        simpa only [Pi.mulSingle_eq_same] using GeneralLinear.UpperUnipotent.entry_diag u i
      · simp [hw]
    · funext w
      change (1 : Matrix (Fin n) (Fin n) ℂ) i i = 1
      exact Matrix.one_apply_eq i

theorem realPlacePoint_mem_unipotent (n : ℕ) (v : RP)
    (u : GeneralLinear.upperUnipotent n ℝ) :
    realPlacePoint F n v u.val ∈ unipotentAdelic F n := by
  rw [Unfolding.mem_unipotentAdelic_iff]
  simp only [realPlacePoint, adelicPoint, MulEquiv.apply_symm_apply]
  have hu := realPlaceGL_isUnitriangular F n v u
  constructor
  · intro i j hij
    change (((archimedeanGLCoordinates F n).symm
      (realPlaceGL F n v u.val)).val i j, (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i j) = 0
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((realPlaceGL F n v u.val).val i j) = 0
      rw [hu.1 hij, map_zero]
    · exact Matrix.one_apply_ne hij.ne'
  · intro i
    change (((archimedeanGLCoordinates F n).symm
      (realPlaceGL F n v u.val)).val i i, (1 : Matrix (Fin n) (Fin n) (FiniteAdeles F)) i i) = 1
    apply Prod.ext
    · change (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm
        ((realPlaceGL F n v u.val).val i i) = 1
      rw [hu.2 i, map_one]
    · exact Matrix.one_apply_eq i

local instance (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (AutomorphicForms F n) :=
  Submodule.addCommGroup _
local instance (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) :=
  Submodule.addCommGroup _
local instance {n : ℕ} (S : OperatorRealization F n) : AddCommGroup S.Space :=
  Submodule.addCommGroup _

variable [CompactSpace (AdeleQuotient F)]

namespace RealPlaceWhittaker

/-- The scheme-valued cusp function evaluates the same actual realized function. -/
theorem cuspFunction_eq_evaluate {r : ℕ} (T : CuspidalOperatorRealization F r)
    (x : T.Space) (z : Points F (r + 1)) :
    cuspFunction F T x z =
      ContinuousRationalFunctions.evaluate F (r + 1) (T.realization.toContinuous x)
        (GeneralLinearGroupPoints.adelicEquiv F (r + 1) z) := by
  have hz := GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F (r + 1)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous x)) z
  rw [LinearEquiv.apply_symm_apply] at hz
  exact hz.symm

set_option maxHeartbeats 1000000 in
theorem cuspFunction_compact {r : ℕ} (T : CuspidalOperatorRealization F r)
    (k : standardInfiniteCompact F (r + 1)) (x : T.Space)
    (z : Points F (r + 1)) :
    cuspFunction F T (T.realization.compactRepresentation k x) z =
      cuspFunction F T x (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
        (AdelicGL.ofInfinite F (r + 1) k.val)) := by
  rw [cuspFunction_eq_evaluate, cuspFunction_eq_evaluate,
    T.realization.evaluate_compactRepresentation, map_mul, MulEquiv.apply_symm_apply]

theorem cuspFunction_smul_apply {r : ℕ} (T : CuspidalOperatorRealization F r)
    (c : ℂ) (x : T.Space) (z : Points F (r + 1)) :
    cuspFunction F T (c • x) z = c * cuspFunction F T x z := by
  simp only [cuspFunction, map_smul]
  rfl

theorem cuspWhittaker_smul_apply {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (c : ℂ) (x : T.Space) (z : Points F (r + 1)) :
    cuspWhittaker F T χ (c • x) z = c * cuspWhittaker F T χ x z := by
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral]
  rw [← integral_const_mul]
  congr 1
  funext q
  simp only [Unfolding.coefficientIntegrand, cuspFunction_smul_apply, mul_assoc]

theorem cuspWhittaker_compact {r : ℕ} (T : CuspidalOperatorRealization F r)
    (χ : AddChar (Adeles F) ℂ) (k : standardInfiniteCompact F (r + 1))
    (x : T.Space) (z : Points F (r + 1)) :
    cuspWhittaker F T χ (T.realization.compactRepresentation k x) z =
      cuspWhittaker F T χ x
        (z * (GeneralLinearGroupPoints.adelicEquiv F (r + 1)).symm
          (AdelicGL.ofInfinite F (r + 1) k.val)) := by
  simp only [cuspWhittaker, generalLinearWhittakerFunction,
    Unfolding.subgroupCharacterCoefficient_eq_integral]
  congr 1
  funext q
  simp only [Unfolding.coefficientIntegrand, cuspFunction_compact, mul_assoc]

end RealPlaceWhittaker

/-- Actual restrictions inherit the scalar compact action as right covariance. -/
theorem IsRealPlaceWhittaker.mul_minusOne {r : ℕ}
    {T : CuspidalOperatorRealization F r} {χ : AddChar (Adeles F) ℂ} {v : RP}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T χ v W) (g : Langlands.GeneralLinear (r + 1) ℝ) :
    W (g * -1) = realMinusOneScalar T v * W g := by
  obtain ⟨x, a, rfl⟩ := hW
  dsimp only
  rw [realPlacePoint_mul]
  have hc := realPlacePoint_finitePoint_commute F (r + 1) v (-1) a
  rw [mul_assoc, hc.eq, ← mul_assoc, realPlacePoint_minusOne]
  rw [← RealPlaceWhittaker.cuspWhittaker_compact]
  change cuspWhittaker F T χ
      (T.realization.realPlaceCompactRepresentation v (-1) x) _ = _
  rw [realMinusOneScalar_action, RealPlaceWhittaker.cuspWhittaker_smul_apply]

/-- Opposite global Whittaker characters cancel on the local unipotent subgroup. -/
theorem IsRealPlaceWhittaker.product_unipotent_mul {r : ℕ}
    {T T' : CuspidalOperatorRealization F r} {χ : AddChar (Adeles F) ℂ} {v : RP}
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hχ : IsStandardAdditiveCharacter F χ)
    (hW : IsRealPlaceWhittaker F T χ v W)
    (hW' : IsRealPlaceWhittaker F T' χ⁻¹ v W')
    (u : GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) :
    W (u.val * g) * W' (u.val * g) = W g * W' g := by
  obtain ⟨x, a, rfl⟩ := hW
  obtain ⟨x', a', rfl⟩ := hW'
  dsimp only
  let z : unipotentAdelic F (r + 1) :=
    ⟨realPlacePoint F (r + 1) v u.val, realPlacePoint_mem_unipotent F (r + 1) v u⟩
  rw [realPlacePoint_mul]
  change cuspWhittaker F T χ x
      (z.val * realPlacePoint F (r + 1) v g * finitePoint F (r + 1) a) *
    cuspWhittaker F T' χ⁻¹ x'
      (z.val * realPlacePoint F (r + 1) v g * finitePoint F (r + 1) a') = _
  rw [mul_assoc, mul_assoc, Unfolding.cuspWhittaker_mul_left F T χ hχ x z,
    Unfolding.cuspWhittaker_mul_left F T' χ⁻¹
      (Unfolding.isStandardAdditiveCharacter_inv F χ hχ) x' z]
  have hn : genericCharacter F r χ (fun _ => 1) z ≠ 0 := by
    have hnorm := Unfolding.norm_genericCharacter F r χ hχ.2.2.2 (fun _ => 1) z
    intro hz
    rw [hz, norm_zero] at hnorm
    exact zero_ne_one hnorm
  have hi : genericCharacter F r χ⁻¹ (fun _ => 1) z =
      (genericCharacter F r χ (fun _ => 1) z)⁻¹ := AddChar.inv_apply' χ _
  rw [hi, mul_mul_mul_comm, mul_inv_cancel₀ hn, one_mul]

/-- The long-Weyl inverse-transpose dual preserves pair-product unipotent invariance. -/
theorem IsRealPlaceWhittaker.dual_product_unipotent_mul {r : ℕ}
    {T T' : CuspidalOperatorRealization F r} {χ : AddChar (Adeles F) ℂ} {v : RP}
    {W W' : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hχ : IsStandardAdditiveCharacter F χ)
    (hW : IsRealPlaceWhittaker F T χ v W)
    (hW' : IsRealPlaceWhittaker F T' χ⁻¹ v W')
    (u : GeneralLinear.upperUnipotent (r + 1) ℝ)
    (g : Langlands.GeneralLinear (r + 1) ℝ) :
    ArchimedeanLocal.dualFunction (r + 1) W (u.val * g) *
        ArchimedeanLocal.dualFunction (r + 1) W' (u.val * g) =
      ArchimedeanLocal.dualFunction (r + 1) W g *
        ArchimedeanLocal.dualFunction (r + 1) W' g := by
  have hu : Unfolding.dualConjGL (r + 1) ℝ u.val ∈
      GeneralLinear.upperUnipotent (r + 1) ℝ := by
    apply Unfolding.isUnitriangular_dualConjGL
    exact (u⁻¹).property
  let ud : GeneralLinear.upperUnipotent (r + 1) ℝ :=
    ⟨Unfolding.dualConjGL (r + 1) ℝ u.val, hu⟩
  have he : GeneralLinear.weylLong (r + 1) ℝ *
      GeneralLinear.inverseTranspose (r + 1) ℝ (u.val * g) =
      ud.val * (GeneralLinear.weylLong (r + 1) ℝ *
        GeneralLinear.inverseTranspose (r + 1) ℝ g) := by
    rw [map_mul]
    simp only [ud, Unfolding.dualConjGL, MulEquiv.trans_apply, MulAut.conj_apply]
    group
  simp only [ArchimedeanLocal.dualFunction, he]
  exact hW.product_unipotent_mul F hχ hW' ud _

/-- The dual function has the same central minus-one scalar. -/
theorem IsRealPlaceWhittaker.dual_mul_minusOne {r : ℕ}
    {T : CuspidalOperatorRealization F r} {χ : AddChar (Adeles F) ℂ} {v : RP}
    {W : Langlands.GeneralLinear (r + 1) ℝ → ℂ}
    (hW : IsRealPlaceWhittaker F T χ v W) (g : Langlands.GeneralLinear (r + 1) ℝ) :
    ArchimedeanLocal.dualFunction (r + 1) W (g * -1) =
      realMinusOneScalar T v * ArchimedeanLocal.dualFunction (r + 1) W g := by
  have hn : GeneralLinear.inverseTranspose (r + 1) ℝ
      (-1 : Langlands.GeneralLinear (r + 1) ℝ) = -1 := by
    apply Units.ext
    simp only [GeneralLinear.inverseTranspose_coe, inv_neg_one, Units.val_neg,
      Units.val_one, Matrix.transpose_neg, Matrix.transpose_one]
  simp only [ArchimedeanLocal.dualFunction, map_mul, hn, ← mul_assoc]
  exact hW.mul_minusOne F _

end Langlands.Global.RankinSelbergGlobal
