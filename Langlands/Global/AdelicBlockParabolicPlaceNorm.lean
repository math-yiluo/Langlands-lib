import Langlands.Global.AdelicBlockParabolicPlace
import Langlands.Global.ArchimedeanPlaceLie

/-! # The determinant normalization at one archimedean place -/

noncomputable section

universe u

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open NumberField Langlands.GeneralLinear ArchimedeanGL RankinSelbergGlobal
open scoped Classical BigOperators NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

variable (F : Type u) [Field F] [NumberField F]

local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

private theorem determinantNorm_single_mixed (n : ℕ) (w : InfinitePlace F)
    (g : ArchimedeanGL F n) (a : ℝ)
    (hr : ∀ v : RP, ‖realPlaceScalarProjection F v g.val.det‖ =
      if v.val = w then a else 1)
    (hc : ∀ v : CP, ‖complexPlaceScalarProjection F v g.val.det‖ =
      if v.val = w then a else 1) :
    ((determinantNorm F n (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm g)) :
      ℝ≥0) : ℝ) = a ^ w.mult := by
  let gInf := (archimedeanGLCoordinates F n).symm g
  let q := Matrix.GeneralLinearGroup.det gInf
  have hq : q.val = (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm g.val.det :=
    ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.map_det _).symm
  have hnorm (v : InfinitePlace F) : ‖q.val v‖ = if v = w then a else 1 := by
    by_cases hv : v.IsReal
    · rw [hq, infiniteAdeleCoordinates_symm_real F _ v hv]
      exact ((InfinitePlace.Completion.isometryEquivRealOfIsReal hv).symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivRealOfIsReal hv).symm) _).trans
        (hr ⟨v, hv⟩)
    · have hv' := InfinitePlace.not_isReal_iff_isComplex.mp hv
      rw [hq, infiniteAdeleCoordinates_symm_complex F _ v hv']
      exact ((InfinitePlace.Completion.isometryEquivComplexOfIsComplex hv').symm.isometry.norm_map_of_map_zero
          (map_zero (InfinitePlace.Completion.ringEquivComplexOfIsComplex hv').symm) _).trans
        (hc ⟨v, hv'⟩)
  rw [determinantNorm_split]
  simp only [AdelicGL.ofInfinite_eq_pair, AdelicGL.infinite_pair, AdelicGL.finite_pair,
    map_one, mul_one]
  change ((IdeleAbsoluteValue.infinite F q : ℝ≥0) : ℝ) = _
  rw [IdeleAbsoluteValue.coe_infinite]
  rw [Finset.prod_eq_single w (fun v _ hv => by rw [hnorm, ite_eq_right hv, one_pow])
    (by simp), hnorm, ite_eq_left rfl]

/-- The normalized adelic determinant restricts at a real place to the absolute determinant. -/
@[simp]
theorem coe_determinantNorm_realPlaceInclusion (n : ℕ) (w : RP)
    (g : Langlands.GeneralLinear n ℝ) :
    ((determinantNorm F n (AdelicGL.realPlaceInclusion F n w g) : ℝ≥0) : ℝ) = |g.val.det| := by
  change ((determinantNorm F n
    (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (realPlaceGL F n w g))) :
    ℝ≥0) : ℝ) = _
  conv_rhs => rw [← pow_one |g.val.det|, ← w.property.mult_eq_one]
  apply determinantNorm_single_mixed
  · intro v
    rw [AlgHom.map_det]
    change ‖((Pi.mulSingle w g : RP → Langlands.GeneralLinear n ℝ) v).val.det‖ = _
    by_cases hv : v = w
    · subst v
      simp only [Pi.mulSingle_eq_same, Real.norm_eq_abs, ite_true]
    · simp only [Pi.mulSingle_eq_of_ne hv, Units.val_one, Matrix.det_one, norm_one,
        ite_eq_right (fun h => hv (Subtype.ext h))]
  · intro v
    rw [AlgHom.map_det]
    change ‖(1 : Matrix (Fin n) (Fin n) ℂ).det‖ = _
    rw [Matrix.det_one, norm_one, ite_eq_right]
    exact fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr v.property) (h ▸ w.property)

/-- The normalized adelic determinant restricts at a complex place to the squared norm. -/
@[simp]
theorem coe_determinantNorm_complexPlaceInclusion (n : ℕ) (w : CP)
    (g : Langlands.GeneralLinear n ℂ) :
    ((determinantNorm F n (AdelicGL.complexPlaceInclusion F n w g) : ℝ≥0) : ℝ) =
      ‖g.val.det‖ ^ 2 := by
  change ((determinantNorm F n
    (AdelicGL.ofInfinite F n ((archimedeanGLCoordinates F n).symm (complexPlaceGL F n w g))) :
    ℝ≥0) : ℝ) = _
  rw [← w.property.mult_eq_two]
  apply determinantNorm_single_mixed
  · intro v
    rw [AlgHom.map_det]
    change ‖(1 : Matrix (Fin n) (Fin n) ℝ).det‖ = _
    rw [Matrix.det_one, norm_one, ite_eq_right]
    exact fun h => (InfinitePlace.not_isReal_iff_isComplex.mpr (h ▸ w.property)) v.property
  · intro v
    rw [AlgHom.map_det]
    change ‖((Pi.mulSingle w g : CP → Langlands.GeneralLinear n ℂ) v).val.det‖ = _
    by_cases hv : v = w
    · subst v
      simp only [Pi.mulSingle_eq_same, ite_true]
    · simp only [Pi.mulSingle_eq_of_ne hv, Units.val_one, Matrix.det_one, norm_one,
        ite_eq_right (fun h => hv (Subtype.ext h))]

variable {n : ℕ} (B : BlockShape n)

private theorem blockDeterminantNorm_apply (m : AdelicBlockParabolic.FullLevi F B)
    (i : Fin B.length) :
    blockDeterminantNorm F B i m = determinantNorm F (B.size i) (m i) := rfl

private theorem coe_leviCharacter (m : AdelicBlockParabolic.FullLevi F B) :
    ((leviCharacter F B m : ℝ≥0) : ℝ) =
      ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        ((blockDeterminantNorm F B i m : ℝ≥0) : ℝ) ^ B.size j /
          ((blockDeterminantNorm F B j m : ℝ≥0) : ℝ) ^ B.size i := by
  rw [leviCharacter_apply]
  simp only [Units.coe_prod, NNReal.coe_prod, Units.val_div_eq_div_val, NNReal.coe_div,
    Units.val_pow_eq_pow_val, NNReal.coe_pow]
  rfl

/-- The pairwise normalized determinant modulus for an actual real block parabolic. -/
def realPlaceModulusValue (p : B.parabolic ℝ) : ℝ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    |(B.leviProjection ℝ p i).val.det| ^ B.size j /
      |(B.leviProjection ℝ p j).val.det| ^ B.size i

/-- The pairwise normalized determinant modulus for an actual complex block parabolic. -/
def complexPlaceModulusValue (p : B.parabolic ℂ) : ℝ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    (‖(B.leviProjection ℂ p i).val.det‖ ^ 2) ^ B.size j /
      (‖(B.leviProjection ℂ p j).val.det‖ ^ 2) ^ B.size i

/-- The global half-twist at a real place is the positive square root of the
pairwise real block determinant formula. -/
theorem coe_parabolicHalfCharacter_realPlace (v : RP) (p : B.parabolic ℝ) :
    (parabolicHalfCharacter F B (AdelicBlockParabolic.realPlaceInclusion F B v p) : ℂ) =
      (Real.sqrt (realPlaceModulusValue B p) : ℂ) := by
  change (leviHalfCharacter F B
    (B.leviProjection (Adeles F) (AdelicBlockParabolic.realPlaceInclusion F B v p)) : ℂ) = _
  rw [coe_leviHalfCharacter, Real.coe_sqrt, coe_leviCharacter,
    AdelicBlockParabolic.leviProjection_realPlaceInclusion]
  simp only [blockDeterminantNorm_apply, coe_determinantNorm_realPlaceInclusion,
    realPlaceModulusValue]

/-- The global half-twist at a complex place uses the squared determinant norm
on each diagonal block. -/
theorem coe_parabolicHalfCharacter_complexPlace (v : CP) (p : B.parabolic ℂ) :
    (parabolicHalfCharacter F B (AdelicBlockParabolic.complexPlaceInclusion F B v p) : ℂ) =
      (Real.sqrt (complexPlaceModulusValue B p) : ℂ) := by
  change (leviHalfCharacter F B
    (B.leviProjection (Adeles F) (AdelicBlockParabolic.complexPlaceInclusion F B v p)) : ℂ) = _
  rw [coe_leviHalfCharacter, Real.coe_sqrt, coe_leviCharacter,
    AdelicBlockParabolic.leviProjection_complexPlaceInclusion]
  simp only [blockDeterminantNorm_apply, coe_determinantNorm_complexPlaceInclusion,
    complexPlaceModulusValue]

end Langlands.Global.AdelicBlockDeterminantCharacter
