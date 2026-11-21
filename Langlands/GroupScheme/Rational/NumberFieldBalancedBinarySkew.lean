import Langlands.GroupScheme.Quaternionic.QuaternionicPureTensorCoefficient
import Langlands.GroupScheme.Quaternionic.SkewHermitianRowRepresentation
import Langlands.GroupScheme.FiniteAlgebraMatrixPoints
import Langlands.LinearAlgebra.QuadraticNormLocalGlobal
import Mathlib.Algebra.Group.Pi.Units

/-! # A binary skew block with proportional values represents every skew value almost everywhere -/

noncomputable section

universe u

open Filter NumberField
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2200000

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic
open FiniteAlgebraUnits.MatrixPoints

variable {F D R : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [Field R] [Algebra F R] (Q : QuatData F D)
  (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)

local notation "E" => field Q.c
local notation "A" => R ⊗[F] D
local notation "barR" => FirstKindInvolution.baseChange τ R

include hbar

private theorem baseChange_ιR (z : E ⊗[F] R) :
    barR (Q.ιR R z) = Q.ιR R ((Q.tensorInvolution R).bar z) := by
  induction z using TensorProduct.inductionOn with
  | tmul a r => rw [Q.ιR_tmul, FirstKindInvolution.baseChange_tmul, hbar, Q.bar_ι,
      Q.tensorInvolution_tmul, Q.ιR_tmul]
  | add a b ha hb => rw [map_add, FirstKindInvolution.map_add, ha, hb, map_add, map_add]

private theorem pure_congruence_of_quadraticNorm (s : F) {a b : R}
    (hab : a ^ 2 - algebraMap F R Q.c * b ^ 2 = algebraMap F R (-s)) :
    ∃ z : A, z * ((1 : R) ⊗ₜ[F] Q.x) * barR z = -((1 : R) ⊗ₜ[F] (s • Q.x)) := by
  let t := (1 : E) ⊗ₜ[F] a + (root : E) ⊗ₜ[F] b
  let r := (root : E) ⊗ₜ[F] (1 : R)
  have hr : Q.ιR R r = (1 : R) ⊗ₜ[F] Q.x := by simp [r, Q.ι_root]
  have ht : t * (Q.tensorInvolution R).bar t = (1 : E) ⊗ₜ[F] (algebraMap F R (-s)) := by
    rw [← hab]
    exact Q.quadraticTensor_mul_conjugate R a b
  refine ⟨Q.ιR R t, ?_⟩
  rw [← hr, Q.baseChange_ιR τ hbar, ← map_mul, ← map_mul, mul_comm t r, mul_assoc, ht,
    show r = (root : E) ⊗ₜ[F] (1 : R) from rfl, Algebra.TensorProduct.tmul_mul_tmul,
    mul_one, one_mul, Q.ιR_tmul, Q.ι_root, map_neg, TensorProduct.neg_tmul,
    Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]

/-- A norm solution with value `-s` makes the binary Gram matrix with diagonal
  `x, s • x` represent every skew coefficient after base change. -/
theorem balancedBinary_represents_of_norm [Invertible (2 : R)] (s : F) (hs : s ≠ 0)
    {a b : R} (hab : a ^ 2 - algebraMap F R Q.c * b ^ 2 = algebraMap F R (-s)) :
    let H : Matrix (Fin 2) (Fin 2) D := Matrix.diagonal ![Q.x, s • Q.x]
    let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
    ∀ c : A, barR c = -c → ∃ y, (barR).matrixSesqBilin M y y = c := by
  dsimp only
  let η : D →ₐ[F] A := Algebra.TensorProduct.includeRight
  let v : Fin 2 → D := ![Q.x, s • Q.x]
  let H := Matrix.diagonal v
  let M := Matrix.diagonal (fun i => η (v i))
  have hM : coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H) = M := by
    ext i j
    rw [coefficientEquiv_tmul]
    by_cases hij : i = j
    · subst j
      simp only [H, M, Matrix.diagonal_apply_eq]
      rfl
    · simp [H, M, Matrix.diagonal_apply_ne _ hij]
  have hx0 : Q.x ≠ 0 := by
    have h := Q.basis.ne_zero 1
    rwa [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1] at h
  have hv (i : Fin 2) : v i ≠ 0 := by
    fin_cases i
    · exact hx0
    · exact smul_ne_zero hs hx0
  have hu : IsUnit M :=
    (Pi.isUnit_iff.mpr fun i => (isUnit_iff_ne_zero.mpr (hv i)).map η).map (Matrix.diagonalRingHom (Fin 2) A)
  have hx : τ Q.x = -Q.x := by
    rw [hbar, ← Q.ι_root, Q.bar_ι, QuadField.conjugation_root, map_neg]
  have hskew (i : Fin 2) : barR (η (v i)) = -η (v i) := by
    change barR ((1 : R) ⊗ₜ[F] v i) = -((1 : R) ⊗ₜ[F] v i)
    rw [FirstKindInvolution.baseChange_tmul, ← TensorProduct.tmul_neg]
    congr 1
    fin_cases i
    · exact hx
    · change τ (s • Q.x) = -(s • Q.x)
      rw [τ.map_smul, hx, smul_neg]
  have hanti : (barR).matrix (Fin 2) M = -M := by
    ext i j
    rw [FirstKindInvolution.matrix_apply, Matrix.neg_apply]
    by_cases hij : i = j
    · subst j
      simpa only [M, Matrix.diagonal_apply_eq] using hskew i
    · simp [M, Matrix.diagonal_apply_ne _ hij, Matrix.diagonal_apply_ne _ (Ne.symm hij),
        FirstKindInvolution.map_zero]
  obtain ⟨z, hz⟩ := Q.pure_congruence_of_quadraticNorm τ hbar s hab
  let e : Fin 2 → A := ![z, 1]
  have he : (barR).matrixSesqBilin M e e = 0 := by
    simp only [FirstKindInvolution.matrixSesqBilin_apply, M, Fin.sum_univ_two,
      Matrix.diagonal_apply_eq, Matrix.diagonal_apply_ne _ (by decide : (0 : Fin 2) ≠ 1),
      Matrix.diagonal_apply_ne _ (by decide : (1 : Fin 2) ≠ 0),
      e, v, Matrix.cons_val_zero, Matrix.cons_val_one, (barR).map_one, mul_zero, zero_mul,
      add_zero, zero_add, one_mul, mul_one]
    change z * ((1 : R) ⊗ₜ[F] Q.x) * barR z + ((1 : R) ⊗ₜ[F] (s • Q.x)) = 0
    rw [hz, neg_add_cancel]
  rw [hM]
  exact FirstKindInvolution.skewHermitianRowRepresentation R A (Fin 2) barR M hanti hu e 1
    (show IsUnit (1 : A) from isUnit_one) he

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.Quaternionic

open KneserThree FiniteAlgebraUnits.MatrixPoints

/-- A binary skew Gram matrix with nonzero proportional diagonal values represents
  every skew value at all but finitely many finite places. -/
def NumberFieldBalancedBinarySkewStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (x : D), x ≠ 0 → τ x = -x → ∀ (s : F), s ≠ 0 →
    ∀ᶠ v : Global.FinitePlace F in cofinite,
      let R := Global.FiniteCompletion F v
      let H : Matrix (Fin 2) (Fin 2) D := Matrix.diagonal ![x, s • x]
      let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
      ∀ c : R ⊗[F] D, τ.baseChange R c = -c → ∃ y, (τ.baseChange R).matrixSesqBilin M y y = c

theorem numberFieldBalancedBinarySkew : NumberFieldBalancedBinarySkewStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ x hx hxτ s hs
  obtain ⟨Q, hQx, hbar⟩ := Quaternion.exists_quatData_of_pure σ hdim hsym two_ne_zero hx hxτ
  have hc : Q.c ≠ 0 := by
    intro h
    have hz := Q.x_mul_x
    rw [h, map_zero] at hz
    exact (mul_ne_zero (hQx.symm ▸ hx) (hQx.symm ▸ hx)) hz
  filter_upwards [Langlands.QuadraticNormLocalGlobal.eventually_exists_eq hc (neg_ne_zero.mpr hs)] with v hv
  obtain ⟨a, b, hab⟩ := hv
  let R := Global.FiniteCompletion F v
  let : CharZero R := Algebra.charZero_of_charZero F R
  let : Invertible (2 : R) := invertibleOfNonzero (two_ne_zero : (2 : R) ≠ 0)
  rw [← hQx]
  exact Q.balancedBinary_represents_of_norm (R := R) τ hbar s hs hab

end Langlands.GroupScheme.Quaternionic
