import Langlands.GroupScheme.Quaternionic.SkewHermitianComponentBaseChange
import Mathlib.RingTheory.AlgebraTower
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-! # The determinant of a symmetric component on a quaternionic line -/

noncomputable section

universe u v w

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1300000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (Q : QuatData F D)

local notation "E" => field Q.c
local notation "κ" => SU3Root.conjugation F E
local notation "δ" => algebraMap F E Q.δ

private theorem ι_mul_j (a : E) : Q.ι a * Q.j = Q.j * Q.ι (κ a) := by
  have h := Q.j_mul_ι (κ a)
  rw [SU3Root.conjugation_involutive] at h
  exact h.symm

private theorem j_mul_j_eq_ι : Q.j * Q.j = Q.ι δ := by
  rw [Q.j_mul_j, AlgHom.commutes]

private theorem j_mul_decomposition (z : D) :
    Q.j * z = Q.j * Q.ι (Q.fst z) + Q.ι (δ * Q.snd z) := by
  conv_lhs => rw [← Q.decompose z, mul_add, ← mul_assoc Q.j Q.j, Q.j_mul_j_eq_ι, ← map_mul]

private theorem mul_j_decomposition (z : D) :
    z * Q.j = Q.j * Q.ι (κ (Q.fst z)) + Q.ι (δ * κ (Q.snd z)) := by
  conv_lhs => rw [← Q.decompose z, add_mul, Q.ι_mul_j, mul_assoc Q.j,
    Q.ι_mul_j, ← mul_assoc Q.j Q.j, Q.j_mul_j_eq_ι, ← map_mul]

private theorem snd_j_mul_any (z : D) : Q.snd (Q.j * z) = Q.fst z := by
  rw [Q.j_mul_decomposition, map_add, Q.snd_j_mul, Q.snd_ι, add_zero]

private theorem snd_mul_j (z : D) : Q.snd (z * Q.j) = κ (Q.fst z) := by
  rw [Q.mul_j_decomposition, map_add, Q.snd_j_mul, Q.snd_ι, add_zero]

private theorem fst_j_mul_any (z : D) : Q.fst (Q.j * z) = δ * Q.snd z := by
  rw [Q.j_mul_decomposition, map_add, Q.fst_j_mul, Q.fst_ι, zero_add]

private theorem bar_j : Q.bar Q.j = -Q.j := by
  have hf : Q.fst Q.j = 0 := by simpa only [map_one, mul_one] using Q.fst_j_mul 1
  have hs : Q.snd Q.j = 1 := by simpa only [map_one, mul_one] using Q.snd_j_mul 1
  rw [bar, hf, hs, map_zero, map_zero, map_one, mul_one, zero_sub]

variable {τ : FirstKindInvolution F D} {V : Type v} [AddCommGroup V]
  [Module D V] [Module F V] [IsScalarTower F D V]
  (B : AntihermitianForm τ V) (hbar : ∀ z, τ z = Q.bar z)

/-- The Gram matrix of the symmetric component on a vector and its `j` multiple. -/
def lineComponentMatrix (x : V) : Matrix (Fin 2) (Fin 2) E :=
  Matrix.of fun i j => Q.symmetricComponent B hbar (![x, Q.j • x] i) (![x, Q.j • x] j)

/-- Its determinant is the conjugate product of the skew-hermitian value, read in
  the chosen quadratic subfield. -/
theorem ι_det_lineComponentMatrix (x : V) :
    Q.ι (Q.lineComponentMatrix B hbar x).det = B x x * τ (B x x) := by
  let z := B x x
  have hpure : Q.bar z = -z := by
    change Q.bar (B x x) = -(B x x)
    rw [← hbar, ← neg_neg (τ (B x x)), ← B.skew x x]
  have hfst := congrArg Q.fst hpure
  rw [Q.fst_bar, map_neg] at hfst
  have h11 : B (Q.j • x) (Q.j • x) = -(Q.j * z * Q.j) := by
    rw [B.smul_left, B.smul_right, hbar, Q.bar_j]
    simp only [mul_neg, mul_assoc]
    rfl
  have h01 : Q.symmetricComponent B hbar x (Q.j • x) = κ (Q.fst z) := by
    rw [← Q.symmetricComponent_swap B hbar x (Q.j • x), Q.symmetricComponent_apply,
      B.smul_left, Q.snd_j_mul_any]
  have h10 : Q.symmetricComponent B hbar (Q.j • x) x = κ (Q.fst z) := by
    rw [Q.symmetricComponent_apply, B.smul_left, Q.snd_j_mul_any]
  have h11' : Q.symmetricComponent B hbar (Q.j • x) (Q.j • x) = -(δ * Q.snd z) := by
    rw [Q.symmetricComponent_apply, h11, map_neg, Q.snd_mul_j, Q.fst_j_mul_any,
      map_neg, SU3Root.conjugation_involutive]
  have hdet : (Q.lineComponentMatrix B hbar x).det = Q.fst z * κ (Q.fst z) - δ * Q.snd z * κ (Q.snd z) := by
    rw [Matrix.det_fin_two]
    change Q.symmetricComponent B hbar x x * Q.symmetricComponent B hbar (Q.j • x) (Q.j • x) -
      Q.symmetricComponent B hbar x (Q.j • x) * Q.symmetricComponent B hbar (Q.j • x) x = _
    rw [h01, h10, h11', Q.symmetricComponent_apply, hfst]
    change κ (Q.snd z) * (-(δ * Q.snd z)) - (-Q.fst z) * (-Q.fst z) = _
    ring
  have hdecomp : Q.elem (Q.fst z) (Q.snd z) = z := Q.decompose z
  have hm := Q.elem_mul_bar (Q.fst z) (Q.snd z)
  rw [hdecomp, ← hbar] at hm
  exact (congrArg Q.ι hdet).trans hm.symm

/-- For the actual quaternion conjugation, the line determinant is the reduced norm. -/
theorem det_lineComponentMatrix_eq_reducedNorm [FiniteDimensional F D] [Algebra.IsCentral F D]
    (hτ : ∀ z : D, z * τ z = algebraMap F D (Langlands.CentralSimple.reducedNorm F D F (1 ⊗ₜ[F] z)))
    (x : V) : (Q.lineComponentMatrix B hbar x).det =
      algebraMap F E (Langlands.CentralSimple.reducedNorm F D F (1 ⊗ₜ[F] B x x)) := by
  apply Q.ι.injective
  change Q.ι (Q.lineComponentMatrix B hbar x).det =
    Q.ι (algebraMap F E (Langlands.CentralSimple.reducedNorm F D F (1 ⊗ₜ[F] B x x)))
  rw [Q.ι_det_lineComponentMatrix, hτ, Q.ι.commutes]

private def coefficientEquiv :
    letI : Module E D := Module.compHom D Q.ι.toRingHom
    D ≃ₗ[E] (Fin 2 → E) := by
  let : Module E D := Module.compHom D Q.ι.toRingHom
  refine { toFun := fun z => ![Q.fst z, κ (Q.snd z)]
           invFun := fun v => Q.elem (v 0) (κ (v 1))
           left_inv := ?_
           right_inv := ?_
           map_add' := ?_
           map_smul' := ?_ }
  · intro x y
    funext i
    fin_cases i
    · exact map_add Q.fst x y
    · change κ (Q.snd (x + y)) = κ (Q.snd x) + κ (Q.snd y)
      rw [map_add, map_add]
  · intro c x
    funext i
    fin_cases i
    · change Q.fst (Q.ι c * x) = c * Q.fst x
      exact Q.fst_ι_mul c x
    · change κ (Q.snd (Q.ι c * x)) = c * κ (Q.snd x)
      rw [Q.snd_ι_mul, map_mul, SU3Root.conjugation_involutive]
  · intro z
    change Q.elem (Q.fst z) (κ (κ (Q.snd z))) = z
    rw [SU3Root.conjugation_involutive]
    exact Q.decompose z
  · intro v
    funext i
    fin_cases i
    · exact Q.fst_mk _ _
    · change κ (Q.snd (Q.elem (v 0) (κ (v 1)))) = v 1
      rw [elem, Q.snd_mk, SU3Root.conjugation_involutive]

/-- The basis of the quaternion algebra over the embedded field, ordered as `1, j`. -/
def coefficientBasis :
    letI : Module E D := Module.compHom D Q.ι.toRingHom
    Module.Basis (Fin 2) E D := by
  let : Module E D := Module.compHom D Q.ι.toRingHom
  exact Module.Basis.ofEquivFun Q.coefficientEquiv

@[simp] theorem coefficientBasis_apply (i : Fin 2) : Q.coefficientBasis i = ![1, Q.j] i := by
  let : Module E D := Module.compHom D Q.ι.toRingHom
  change Module.Basis.ofEquivFun Q.coefficientEquiv i = _
  rw [Module.Basis.coe_ofEquivFun]
  fin_cases i
  · change Q.elem ((Pi.single (0 : Fin 2) (1 : E) : Fin 2 → E) 0)
      (κ ((Pi.single (0 : Fin 2) (1 : E) : Fin 2 → E) 1)) = 1
    simp [elem]
  · change Q.elem ((Pi.single (1 : Fin 2) (1 : E) : Fin 2 → E) 0)
      (κ ((Pi.single (1 : Fin 2) (1 : E) : Fin 2 → E) 1)) = Q.j
    simp [elem]

variable {ι : Type w}

/-- A division-algebra basis gives a quadratic-field basis by using `1, j` on each line. -/
def componentBasis (b : Module.Basis ι D V) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    Module.Basis (Fin 2 × ι) E V := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : Module E D := Module.compHom D Q.ι.toRingHom
  let : IsScalarTower E D V := ⟨fun e d v => by
    change (Q.ι e * d) • v = Q.ι e • (d • v)
    exact mul_smul _ _ _⟩
  exact Q.coefficientBasis.smulTower b

omit [Module F V] [IsScalarTower F D V] in
@[simp] theorem componentBasis_apply (b : Module.Basis ι D V) (i : Fin 2) (j : ι) :
    Q.componentBasis b (i, j) = (![1, Q.j] i) • b j := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  let : Module E D := Module.compHom D Q.ι.toRingHom
  let : IsScalarTower E D V := ⟨fun e d v => by
    change (Q.ι e * d) • v = Q.ι e • (d • v)
    exact mul_smul _ _ _⟩
  change (Q.coefficientBasis.smulTower b) (i, j) = _
  rw [Module.Basis.smulTower_apply, Q.coefficientBasis_apply]

/-- The determinant on the field basis from an orthogonal division basis is the
  scalar extension of the product of the reduced norms of its diagonal values. -/
theorem det_componentBasis_eq_prod_reducedNorm [FiniteDimensional F D] [Algebra.IsCentral F D]
    [Fintype ι] [DecidableEq ι]
    (hτ : ∀ z : D, z * τ z = algebraMap F D (Langlands.CentralSimple.reducedNorm F D F (1 ⊗ₜ[F] z)))
    (b : Module.Basis ι D V) (hb : ∀ i j, i ≠ j → B (b i) (b j) = 0) :
    letI : Module E V := Module.compHom V Q.ι.toRingHom
    (LinearMap.toMatrix₂ (Q.componentBasis b) (Q.componentBasis b) (Q.symmetricComponent B hbar)).det =
      algebraMap F E (∏ i, Langlands.CentralSimple.reducedNorm F D F (1 ⊗ₜ[F] B (b i) (b i))) := by
  let : Module E V := Module.compHom V Q.ι.toRingHom
  have hmat : LinearMap.toMatrix₂ (Q.componentBasis b) (Q.componentBasis b) (Q.symmetricComponent B hbar) =
      Matrix.blockDiagonal (fun i => Q.lineComponentMatrix B hbar (b i)) := by
    ext ⟨i, k⟩ ⟨j, l⟩
    rw [LinearMap.toMatrix₂_apply, Q.componentBasis_apply, Q.componentBasis_apply, Matrix.blockDiagonal_apply']
    by_cases h : k = l
    · subst l
      rw [ite_eq_left rfl]
      fin_cases i <;> fin_cases j <;> simp [lineComponentMatrix]
    · rw [ite_eq_right h, symmetricComponent_apply, B.smul_left, B.smul_right, hb k l h]
      simp
  rw [hmat, Matrix.det_blockDiagonal, map_prod]
  apply Finset.prod_congr rfl
  intro i _
  exact Q.det_lineComponentMatrix_eq_reducedNorm B hbar hτ (b i)

end Langlands.GroupScheme.KneserThree.QuatData
