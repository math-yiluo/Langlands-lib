import Langlands.Global.ArchimedeanCharacterGrowth
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Representation.Archimedean.Kostant.Center

/-! # Real sign representatives and scalar Lie flows -/

noncomputable section

universe u

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

open NumberField Langlands.Archimedean.Kostant

variable (F : Type u) [Field F]

local notation "R" => mixedEmbedding.mixedSpace F
local notation "RP" => {v : InfinitePlace F // InfinitePlace.IsReal v}
local notation "CP" => {v : InfinitePlace F // InfinitePlace.IsComplex v}

private def mixedRealSign (s : RP → Bool) : R :=
  (fun v => if s v then -1 else 1, 1)

private theorem mixedRealSign_sq (s : RP → Bool) : mixedRealSign F s * mixedRealSign F s = 1 := by
  apply Prod.ext
  · funext v
    change (if s v then (-1 : ℝ) else 1) * (if s v then -1 else 1) = 1
    split <;> simp
  · change (1 : CP → ℂ) * 1 = 1
    exact one_mul 1

/-- The signs at the real places, with component one at all complex places. -/
def mixedRealSignUnit (s : RP → Bool) : Rˣ where
  val := mixedRealSign F s
  inv := mixedRealSign F s
  val_inv := mixedRealSign_sq F s
  inv_val := mixedRealSign_sq F s

variable [NumberField F]

/-- Every mixed archimedean unit is a real sign vector times an exponential unit. -/
theorem exists_sign_mul_expUnit (a : Rˣ) :
    ∃ (s : RP → Bool) (x : R), a = mixedRealSignUnit F s * banachExpUnit x := by
  let s (v : RP) := decide ((a : R).1 v < 0)
  let x : R := (fun v => Real.log ((a : R).1 v), fun w => Complex.log ((a : R).2 w))
  refine ⟨s, x, ?_⟩
  apply Units.ext
  apply Prod.ext
  · funext v
    change (a : R).1 v = (if s v then (-1 : ℝ) else 1) * (NormedSpace.exp x).1 v
    rw [exp_mixedSpace_fst_apply, show x.1 v = Real.log ((a : R).1 v) from rfl]
    have hne := units_fst_ne_zero a v
    by_cases h : (a : R).1 v < 0
    · simp [s, h, Real.exp_log_of_neg h]
    · have hp : 0 < (a : R).1 v := lt_of_le_of_ne (le_of_not_gt h) hne.symm
      simp [s, h, Real.exp_log hp]
  · funext w
    change (a : R).2 w = (1 : ℂ) * (NormedSpace.exp x).2 w
    rw [one_mul, exp_mixedSpace_snd_apply, show x.2 w = Complex.log ((a : R).2 w) from rfl,
      Complex.exp_log (units_snd_ne_zero a w)]

/-- Regard the units in mixed coordinates as the actual units of the infinite adeles. -/
def mixedUnitToInfinite : Rˣ ≃* (InfiniteAdeles F)ˣ :=
  Units.mapEquiv (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toMulEquiv

variable (n : ℕ)

/-- The real Lie direction whose matrix is scalar multiplication by `x`. -/
def scalarDirection (x : R) : RealLieAlgebra F n :=
  (realLieAlgebraToMatrix F n).symm (x • (1 : ArchimedeanMatrix F n))

omit [NumberField F] in
private theorem scalarDirection_lie (x : R) (X : RealLieAlgebra F n) :
    ⁅scalarDirection F n x, X⁆ = 0 := by
  apply (realLieAlgebraToMatrix F n).injective
  rw [realLieAlgebraToMatrix_lie, scalarDirection, LinearEquiv.apply_symm_apply,
    Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, sub_self, map_zero]

omit [NumberField F] in
private theorem complexify_scalarDirection_lie (x : R) (X : ComplexLieAlgebra F n) :
    ⁅complexify F n (scalarDirection F n x), X⁆ = 0 := by
  induction X using TensorProduct.inductionOn with
  | tmul c Y =>
    rw [complexify_apply, complexLieAlgebra_lie_tmul, scalarDirection_lie, TensorProduct.tmul_zero]
  | add X Y hX hY =>
    exact (lie_add (L := ComplexLieAlgebra F n) (M := ComplexLieAlgebra F n) _ X Y).trans
      (by rw [hX, hY, add_zero])

/-- The real scalar direction gives a central element of the complex enveloping algebra. -/
def scalarDirectionCenter (x : R) : EnvelopingCenter F n :=
  ⟨envelopingGenerator F n (complexify F n (scalarDirection F n x)), by
    apply mem_center_of_commute
    intro X
    have h := envelopingGenerator_lie F n (complexify F n (scalarDirection F n x)) X
    rw [complexify_scalarDirection_lie, map_zero] at h
    exact (sub_eq_zero.mp h.symm).symm⟩

/-- The scalar Lie exponential in the actual infinite adelic group is the scalar
matrix of the exponential unit. -/
theorem infiniteOneParameter_scalarDirection (x : R) (t : ℝ) :
    infiniteOneParameter F n (scalarDirection F n x) t =
      Matrix.GeneralLinearGroup.scalar (Fin n) (mixedUnitToInfinite F (banachExpUnit (t • x))) := by
  apply (archimedeanGLCoordinates F n).injective
  apply Units.ext
  let L := Matrix.scalarAlgHom (Fin n) ℝ (α := R)
  have hL (y : R) : L y = y • (1 : ArchimedeanMatrix F n) := by
    apply Matrix.ext
    intro i j
    simp only [L, Matrix.scalarAlgHom_apply, Matrix.scalar_apply, Matrix.diagonal_apply,
      Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
    split_ifs <;> simp
  have he := NormedSpace.map_exp_of_mem_ball (𝕂 := ℝ) L
    L.toLinearMap.toContinuousLinearMap.continuous (t • x)
    ((NormedSpace.expSeries_radius_eq_top ℝ R).symm ▸ edist_lt_top _ _)
  rw [infiniteOneParameter, ContinuousMulEquiv.apply_symm_apply, oneParameter_val,
    scalarDirection, LinearEquiv.apply_symm_apply]
  have ht : t • (x • (1 : ArchimedeanMatrix F n)) = L (t • x) := by rw [hL, smul_assoc]
  rw [ht, ← he]
  apply Matrix.ext
  intro i j
  let E := InfiniteAdeleRing.ringEquiv_mixedSpace F
  change Matrix.scalar (Fin n) (NormedSpace.exp (t • x)) i j =
    E (Matrix.scalar (Fin n) (E.symm (NormedSpace.exp (t • x))) i j)
  simp only [Matrix.scalar_apply, Matrix.diagonal_apply]
  split_ifs
  · exact (E.apply_symm_apply _).symm
  · exact (map_zero E).symm

end Langlands.Global.ArchimedeanGL
