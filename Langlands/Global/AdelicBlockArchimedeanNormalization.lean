import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.ArchimedeanCharacterSmoothness

/-!
# Smooth archimedean extension of the adelic block half character

The positive adelic half character on the infinite parabolic is evaluated
by a smooth function of its mixed-coordinate diagonal blocks.
-/

noncomputable section

open scoped BigOperators Classical ContDiff Matrix.Norms.Operator NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Langlands.Global.AdelicBlockDeterminantCharacter

open Langlands.GeneralLinear AdelicBlockParabolic NumberField

private def complexHalf : ℝ≥0ˣ →ₜ* ℂˣ where
  toMonoidHom := Jacquet.complexCharacter
    (Jacquet.positiveHalfCharacter (MonoidHom.id ℝ≥0ˣ))
  continuous_toFun := (Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map.comp
    NNReal.continuous_sqrt.units_map

variable (F : Type u) [Field F] [NumberField F]

/-- The positive half of the normalized infinite idelic norm in mixed coordinates. -/
def mixedHalfNorm : (mixedEmbedding.mixedSpace F)ˣ →ₜ* ℂˣ :=
  complexHalf.comp ((IdeleAbsoluteValue.infinite F).comp
    { toMonoidHom := Units.map
        (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom
      continuous_toFun := (continuous_infiniteAdeleCoordinates_symm F).units_map _ })

variable {n : ℕ} (B : BlockShape n)

/-- Extract a diagonal block in the actual mixed matrix coordinates. -/
def archimedeanDiagonalBlock (i : Fin B.length) :
    ArchimedeanMatrix F n →L[ℝ] ArchimedeanMatrix F (B.size i) :=
  (show ArchimedeanMatrix F n →ₗ[ℝ] ArchimedeanMatrix F (B.size i) from
    { toFun := fun x a b => x (B.index i a) (B.index i b)
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }).toContinuousLinearMap

private def blockHalf (i : Fin B.length) (x : ArchimedeanMatrix F n) : ℂ :=
  unitsCharacterExtension (mixedHalfNorm F) (archimedeanDiagonalBlock F B i x).det

/-- An ambient mixed-matrix extension of the positive normalized half
character on the infinite parabolic. -/
def archimedeanHalfExtension (x : ArchimedeanMatrix F n) : ℂ :=
  ∏ i : Fin B.length, ∏ j ∈ Finset.univ.filter (fun j => i < j),
    blockHalf F B i x ^ B.size j / blockHalf F B j x ^ B.size i

local notation "μ" => (B.leviProjection (InfiniteAdeles F))

private theorem archimedeanDiagonalBlock_parabolic (p : Infinite F B) (i : Fin B.length) :
    archimedeanDiagonalBlock F B i (archimedeanGLCoordinates F n p.val).val =
      (archimedeanGLCoordinates F (B.size i) (μ p i)).val := rfl

private theorem blockHalf_parabolic (p : Infinite F B) (i : Fin B.length) :
    blockHalf F B i (archimedeanGLCoordinates F n p.val).val =
      (mixedHalfNorm F (Matrix.GeneralLinearGroup.det
        (archimedeanGLCoordinates F (B.size i) (μ p i))) : ℂ) := by
  rw [blockHalf, archimedeanDiagonalBlock_parabolic, ← Matrix.GeneralLinearGroup.val_det_apply,
    unitsCharacterExtension_unit]

private theorem blockDeterminantNorm_ofInfinite_leviProjection (p : Infinite F B) (i : Fin B.length) :
    blockDeterminantNorm F B i (B.leviProjection (Adeles F) (ofInfinite F B p)) =
      infiniteDeterminantNorm F (B.size i) (μ p i) := by
  have h : B.leviProjection (Adeles F) (ofInfinite F B p) = leviPair F B (μ p) 1 := by
    change B.leviProjection (Adeles F) (pair F B p 1) = _
    rw [leviProjection_pair, map_one]
  rw [h]
  change IdeleAbsoluteValue.full F
    (AdelicGL.determinant F (B.size i) (AdelicGL.ofInfinite F (B.size i) (μ p i))) = _
  rw [AdelicGL.determinant_ofInfinite, IdeleAbsoluteValue.full_infiniteIdelesInclusion]
  rfl

private theorem mixedHalfNorm_det (s : ℕ) (g : InfiniteAdelicGL F s) :
    mixedHalfNorm F (Matrix.GeneralLinearGroup.det (archimedeanGLCoordinates F s g)) =
      complexHalf (infiniteDeterminantNorm F s g) := by
  change complexHalf (IdeleAbsoluteValue.infinite F (Units.map
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom
    (Matrix.GeneralLinearGroup.det (archimedeanGLCoordinates F s g)))) = _
  have hd := Matrix.GeneralLinearGroup.map_det
    (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom (archimedeanGLCoordinates F s g)
  exact congrArg (fun z => complexHalf (IdeleAbsoluteValue.infinite F z))
    (hd.symm.trans (congrArg (fun a : InfiniteAdelicGL F s => Matrix.GeneralLinearGroup.det a)
      ((archimedeanGLCoordinates F s).symm_apply_apply g)))

theorem archimedeanHalfExtension_parabolic (p : Infinite F B) :
    archimedeanHalfExtension F B (archimedeanGLCoordinates F n p.val).val =
      (parabolicHalfCharacter F B (ofInfinite F B p) : ℂ) := by
  let m := B.leviProjection (Adeles F) (ofInfinite F B p)
  have hd (i : Fin B.length) : determinantNorm F (B.size i) (m i) =
      infiniteDeterminantNorm F (B.size i) (μ p i) :=
    blockDeterminantNorm_ofInfinite_leviProjection F B p i
  change archimedeanHalfExtension F B (archimedeanGLCoordinates F n p.val).val =
    (complexHalf (leviCharacter F B m) : ℂ)
  rw [archimedeanHalfExtension, leviCharacter_apply]
  simp only [blockHalf_parabolic, mixedHalfNorm_det, map_prod, map_div, map_pow,
    Units.coe_prod, Units.val_div_eq_div_val, Units.val_pow_eq_pow_val]
  exact Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun j _ => by rw [hd i, hd j]

set_option maxHeartbeats 650000 in
/-- In the actual mixed matrix coordinates the extension is smooth at every
infinite parabolic matrix. -/
theorem contDiffAt_archimedeanHalfExtension (p : Infinite F B) :
    ContDiffAt ℝ ∞ (archimedeanHalfExtension F B) (archimedeanGLCoordinates F n p.val).val := by
  have hs (i : Fin B.length) : ContDiffAt ℝ ∞ (blockHalf F B i)
      (archimedeanGLCoordinates F n p.val).val := by
    have h := contDiffAt_unitsCharacterExtension (mixedHalfNorm F) (Matrix.GeneralLinearGroup.det
      (archimedeanGLCoordinates F (B.size i) (μ p i)))
    rw [Matrix.GeneralLinearGroup.val_det_apply, ← archimedeanDiagonalBlock_parabolic F B p i] at h
    let x := (archimedeanGLCoordinates F n p.val).val
    have hd : ContDiffAt ℝ ∞ (fun y => (archimedeanDiagonalBlock F B i y).det) x :=
      (contDiff_archimedeanDet F (B.size i)).contDiffAt.comp x
        (archimedeanDiagonalBlock F B i).contDiff.contDiffAt
    exact h.comp x hd
  have hne (i : Fin B.length) :
      blockHalf F B i (archimedeanGLCoordinates F n p.val).val ≠ 0 := by
    rw [blockHalf_parabolic]
    exact Units.ne_zero _
  unfold archimedeanHalfExtension
  apply contDiffAt_prod
  intro i _
  apply contDiffAt_prod
  intro j _
  simp only [div_eq_mul_inv]
  exact ((hs i).pow (B.size j)).mul
    (((hs j).pow (B.size i)).fun_inv (pow_ne_zero _ (hne j)))

end Langlands.Global.AdelicBlockDeterminantCharacter
