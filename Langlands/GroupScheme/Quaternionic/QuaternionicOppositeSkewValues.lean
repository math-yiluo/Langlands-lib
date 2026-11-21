import Langlands.GroupScheme.Quaternionic.QuaternionicSplitOppositeValues
import Langlands.GroupScheme.Quaternionic.QuaternionCoefficientDichotomy
import Langlands.GroupScheme.Quaternionic.SkewHermitianOrthogonalBasis
import Langlands.GroupScheme.Quaternionic.SkewHermitianRowRepresentation
import Langlands.GroupScheme.Quaternionic.SplittingMatrix
import Langlands.GroupScheme.Quaternionic.KneserThreeQuaternion

/-! # Opposite invertible skew values after scalar extension -/

noncomputable section

universe u v w z

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2000000

section Division

variable {R : Type u} {A : Type v} [Field R] [DivisionRing A] [Algebra R A]
  [Invertible (2 : R)] (τ : FirstKindInvolution R A)
  {I : Type w} [Fintype I] [DecidableEq I] [Nonempty I]

private theorem exists_unit_self (hne : ∃ c : A, τ c ≠ c) {H : Matrix I I A}
    (hH : τ.matrix I H = -H) (hu : IsUnit H) :
    ∃ x : I → A, IsUnit (τ.matrixSesqBilin H x x) := by
  have hs : τ.IsAntihermitian H := by
    refine ⟨hH, fun i => KneserThree.mem_alternatingSubspace_of_neg τ (h := ⅟ (2 : R)) (mul_invOf_self _) ?_⟩
    exact congrArg (fun P : Matrix I I A => P i i) hH
  obtain ⟨x, hx⟩ := (AntihermitianForm.ofMatrix hs).exists_self_ne_zero hne
    (AntihermitianForm.ofMatrix_separatingLeft hs hu)
  exact ⟨x, isUnit_iff_ne_zero.mpr hx⟩

omit [Nonempty I] in
private theorem represents_of_isotropic {H : Matrix I I A} (hH : τ.matrix I H = -H)
    (hu : IsUnit H) {x : I → A} (hx : x ≠ 0) (hxx : τ.matrixSesqBilin H x x = 0)
    (c : A) (hc : τ c = -c) : ∃ y : I → A, τ.matrixSesqBilin H y y = c := by
  obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := not_forall.mp (fun h => hx (funext h))
  exact skewHermitianRowRepresentation R A I τ H hH hu x i (isUnit_iff_ne_zero.mpr hi) hxx c hc

variable {L : Type z} [Fintype L] [DecidableEq L] [Nonempty L]

private theorem divisionSkew_exists_opposite_unit_values (hne : ∃ c : A, τ c ≠ c)
    {H : Matrix I I A} {G : Matrix L L A}
    (hH : τ.matrix I H = -H) (hG : τ.matrix L G = -G) (huH : IsUnit H) (huG : IsUnit G)
    (x y : I → A) (a b : L → A)
    (hzero : τ.matrixSesqBilin H x x + τ.matrixSesqBilin G a a = 0)
    (hone : τ.matrixSesqBilin H x y + τ.matrixSesqBilin G a b = 1) :
    ∃ (r : I → A) (s : L → A), IsUnit (-(τ.matrixSesqBilin G s s)) ∧
      τ.matrixSesqBilin H r r = -(τ.matrixSesqBilin G s s) := by
  have h := eq_neg_of_add_eq_zero_left hzero
  by_cases hh : τ.matrixSesqBilin H x x = 0
  · have hg : τ.matrixSesqBilin G a a = 0 := by simpa only [hh, zero_add] using hzero
    by_cases hx : x = 0
    · have ha : a ≠ 0 := by
        intro hz
        simp only [hx, hz, _root_.map_zero, LinearMap.zero_apply, add_zero] at hone
        exact zero_ne_one hone
      obtain ⟨r, hr⟩ := τ.exists_unit_self hne hH huH
      have hc : τ (-(τ.matrixSesqBilin H r r)) = -(-(τ.matrixSesqBilin H r r)) := by
        rw [τ.map_neg, neg_neg]
        exact (τ.matrixSesqBilin_swap_of_skew hH r r).symm
      obtain ⟨s, hs⟩ := τ.represents_of_isotropic hG huG ha hg _ hc
      exact ⟨r, s, by rw [hs, neg_neg]; exact hr, by rw [hs, neg_neg]⟩
    · obtain ⟨s, hs⟩ := τ.exists_unit_self hne hG huG
      have hc : τ (-(τ.matrixSesqBilin G s s)) = -(-(τ.matrixSesqBilin G s s)) := by
        rw [τ.map_neg, neg_neg]
        exact (τ.matrixSesqBilin_swap_of_skew hG s s).symm
      obtain ⟨r, hr⟩ := τ.represents_of_isotropic hH huH hx hh _ hc
      exact ⟨r, s, hs.neg, hr⟩
  · exact ⟨x, a, h ▸ isUnit_iff_ne_zero.mpr hh, h⟩

end Division

section Coefficients

variable {F D R : Type u} [Field F] [DivisionRing D] [Algebra F D] [Field R] [Algebra F R]
  {I : Type} [Fintype I] [DecidableEq I]

/-- The skew Gram relation survives the coefficient chart of a scalar extension. -/
theorem matrix_coefficientEquiv_tmul_eq_neg (τ : FirstKindInvolution F D)
    {H : Matrix I I D} (hH : τ.matrix I H = -H) :
    let M := coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)
    (τ.baseChange R).matrix I M = -M := by
  intro M
  ext i j
  change τ.baseChange R (M j i) = -(M i j)
  rw [← τ.coefficientEquiv_baseChange R ((1 : R) ⊗ₜ[F] H) i j,
    FirstKindInvolution.baseChange_tmul, hH, TensorProduct.tmul_neg, _root_.map_neg, Matrix.neg_apply]

/-- Invertibility of a Gram matrix survives the coefficient chart of scalar extension. -/
theorem isUnit_coefficientEquiv_tmul {H : Matrix I I D} (hH : IsUnit H) :
    IsUnit (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)) :=
  (hH.map (Algebra.TensorProduct.includeRight : Matrix I I D →ₐ[F] R ⊗[F] Matrix I I D)).map
    (coefficientEquiv F D R)

end Coefficients

section Quaternion

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
  (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)

local notation "A" => R ⊗[F] D
local notation "τR" => FirstKindInvolution.baseChange (σ.quaternionConjugation hdim hsym) R

omit [Algebra.IsCentral F D] in
/-- Canonical quaternion conjugation remains nontrivial after extending the field. -/
theorem quaternionConjugation_baseChange_ne_id : ∃ a : A, τR a ≠ a := by
  let l := σ.quaternionAlternatingUnit hdim hsym
  refine ⟨(1 : R) ⊗ₜ[F] (l : D), ?_⟩
  rw [FirstKindInvolution.baseChange_tmul, KneserThree.Quaternion.conj_ell]
  intro hh
  have hinj : Function.Injective (fun a : D => (1 : R) ⊗ₜ[F] a) :=
    Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
  have h := congrArg (fun z : D => z + l) (hinj hh)
  rw [neg_add_cancel, ← two_smul F] at h
  exact (smul_ne_zero (two_ne_zero : (2 : F) ≠ 0) l.ne_zero) h.symm

/-- For each field extension, a normalized isotropic row in an orthogonal sum
  of two nonzero skew spaces yields opposite invertible values. -/
theorem quaternionic_exists_opposite_unit_values
    {I : Type w} [Fintype I] [DecidableEq I] [Nonempty I]
    {L : Type z} [Fintype L] [DecidableEq L] [Nonempty L]
    {H : Matrix I I A} {G : Matrix L L A}
    (hH : (τR).matrix I H = -H) (hG : (τR).matrix L G = -G) (huH : IsUnit H) (huG : IsUnit G)
    (x y : I → A) (a b : L → A)
    (hzero : (τR).matrixSesqBilin H x x + (τR).matrixSesqBilin G a a = 0)
    (hone : (τR).matrixSesqBilin H x y + (τR).matrixSesqBilin G a b = 1) :
    ∃ (r : I → A) (s : L → A), IsUnit (-((τR).matrixSesqBilin G s s)) ∧
      (τR).matrixSesqBilin H r r = -((τR).matrixSesqBilin G s s) := by
  let : CharZero R := charZero_of_injective_algebraMap (algebraMap F R).injective
  let : Invertible (2 : R) := invertibleOfNonzero two_ne_zero
  rcases quaternionCoefficientDichotomy F D R hdim with hdom | he
  · let : IsDomain A := hdom
    let : DivisionRing A := divisionRingOfFiniteDimensional R A
    exact divisionSkew_exists_opposite_unit_values τR (σ.quaternionConjugation_baseChange_ne_id hdim hsym)
      hH hG huH huG x y a b hzero hone
  · let e := he.some
    exact splitSkew_exists_opposite_unit_values e τR (σ.splitQuaternionConjugation_mul_gramTwo hdim hsym e)
      two_ne_zero hH hG huH huG x y a b hzero hone

end Quaternion

/-- Over a scalar extension of a quaternion division algebra in characteristic
  zero, two nonzero skew spaces with a normalized isotropic row in their sum
  have opposite invertible values. -/
def QuaternionicOppositeSkewValuesStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Field R] [Algebra F R]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let A := R ⊗[F] D
    let τ := (σ.quaternionConjugation hdim hsym).baseChange R
    ∀ (I : Type w) (L : Type z) [Fintype I] [DecidableEq I] [Nonempty I]
      [Fintype L] [DecidableEq L] [Nonempty L]
      (H : Matrix I I A) (G : Matrix L L A),
      τ.matrix I H = -H → τ.matrix L G = -G → IsUnit H → IsUnit G →
      ∀ (x y : I → A) (a b : L → A),
        τ.matrixSesqBilin H x x + τ.matrixSesqBilin G a a = 0 →
        τ.matrixSesqBilin H x y + τ.matrixSesqBilin G a b = 1 →
        ∃ (r : I → A) (s : L → A), IsUnit (-(τ.matrixSesqBilin G s s)) ∧
          τ.matrixSesqBilin H r r = -(τ.matrixSesqBilin G s s)

theorem quaternionicOppositeSkewValues : QuaternionicOppositeSkewValuesStatement.{u, w, z} := by
  intro F D R _ _ _ _ _ _ _ _ σ hdim hsym A τ I L _ _ _ _ _ _ H G hH hG huH huG x y a b hx hxy
  exact σ.quaternionic_exists_opposite_unit_values hdim hsym hH hG huH huG x y a b hx hxy

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
