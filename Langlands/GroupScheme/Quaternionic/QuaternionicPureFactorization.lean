import Langlands.GroupScheme.Quaternionic.KneserThreeUnits
import Langlands.GroupScheme.Quaternionic.QuaternionConjugation
import Langlands.GroupScheme.Quaternionic.MatrixReducedNorm
import Mathlib.Algebra.Group.Pi.Units

/-! # Products of pure quaternions and rank-three Gram models -/

noncomputable section

universe u

open Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open Langlands.CentralSimple FiniteAlgebraUnits.MatrixPoints

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1700000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  [FiniteDimensional F D] (σ : FirstKindInvolution F D)

/-- The alternating space of quaternion conjugation has dimension three. -/
theorem finrank_quaternionConjugation_alternating [Algebra.IsCentral F D] [Invertible (2 : F)]
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3) :
    Module.finrank F (σ.quaternionConjugation hdim hsym).alternatingSubspace = 3 := by
  let τ := σ.quaternionConjugation hdim hsym
  let l := σ.quaternionAlternatingUnit hdim hsym
  have hl := σ.quaternionAlternatingUnit_mem hdim hsym
  have hrange : τ.symmetricSubspace = LinearMap.range (Algebra.linearMap F D) := by
    ext x
    rw [τ.mem_symmetricSubspace, LinearMap.mem_range]
    constructor
    · intro hx
      let t := σ.alternatingTrace (σ.finrank_alternatingSubspace_of_dimensions hdim hsym) l hl x
      have ht : algebraMap F D t = x + τ x :=
        σ.alternatingTrace_spec (σ.finrank_alternatingSubspace_of_dimensions hdim hsym) l hl x
      refine ⟨⅟ (2 : F) * t, ?_⟩
      change algebraMap F D (⅟ (2 : F) * t) = x
      rw [_root_.map_mul, ht, hx, ← two_smul F, ← Algebra.smul_def, smul_smul,
        invOf_mul_self, one_smul]
    · rintro ⟨t, rfl⟩
      exact τ.map_algebraMap t
  have hτ : Module.finrank F τ.symmetricSubspace = 1 := by
    rw [hrange, LinearMap.finrank_range_of_inj (algebraMap F D).injective, Module.finrank_self]
  have hker : LinearMap.ker (LinearMap.id - τ.toLinearMap) = τ.symmetricSubspace := by
    ext x
    change x - τ x = 0 ↔ τ x - x = 0
    rw [sub_eq_zero, sub_eq_zero]
    exact eq_comm
  have h := (LinearMap.id - τ.toLinearMap).finrank_range_add_finrank_ker
  rw [hker, hτ, hdim] at h
  change Module.finrank F τ.alternatingSubspace + 1 = 4 at h
  change Module.finrank F τ.alternatingSubspace = 3
  omega

/-- For a three-dimensional alternating space in a quaternion division algebra,
  every nonzero element is a product of two nonzero alternating elements. -/
theorem exists_mul_of_alternating [Invertible (2 : F)] (hdim : Module.finrank F D = 4)
    (hσ : Module.finrank F σ.alternatingSubspace = 3) (a : D) (ha : a ≠ 0) :
    ∃ p q : D, p ∈ σ.alternatingSubspace ∧ q ∈ σ.alternatingSubspace ∧
      p ≠ 0 ∧ q ≠ 0 ∧ p * q = a := by
  let P := σ.alternatingSubspace
  let f := (Units.mk0 a ha).mulLeftLinearEquiv F D
  let W := P.map f.toLinearMap
  have hW : Module.finrank F W = 3 := (f.finrank_map_eq P).trans hσ
  have hsum := P.finrank_sup_add_finrank_inf_eq W
  have hle := (P ⊔ W).finrank_le
  rw [hdim] at hle
  have hpos : 0 < Module.finrank F (P ⊓ W : Submodule F D) := by
    change Module.finrank F (P ⊔ W : Submodule F D) + Module.finrank F (P ⊓ W : Submodule F D) =
      Module.finrank F P + Module.finrank F W at hsum
    rw [hW, show Module.finrank F P = 3 from hσ] at hsum
    omega
  obtain ⟨p, hp, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (show (P ⊓ W : Submodule F D) ≠ ⊥ from by
    intro h
    rw [h, finrank_bot] at hpos
    omega)
  obtain ⟨y, hy, hpy⟩ := Submodule.mem_map.mp hp.2
  change a * y = p at hpy
  have hy0 : y ≠ 0 := by
    intro h
    exact hp0 (hpy.symm.trans (by rw [h, mul_zero]))
  have hy' : σ y = -y := by
    obtain ⟨b, rfl⟩ := σ.mem_alternatingSubspace.mp hy
    rw [σ.map_sub, σ.apply_apply, neg_sub]
  have hm : σ y⁻¹ * y = -1 := by
    have h := σ.map_mul y y⁻¹
    rw [mul_inv_cancel₀ hy0, σ.map_one, hy', mul_neg] at h
    calc
      σ y⁻¹ * y = -(-(σ y⁻¹ * y)) := (neg_neg _).symm
      _ = -1 := congrArg Neg.neg h.symm
  have hq : σ y⁻¹ = -y⁻¹ := by
    calc
      σ y⁻¹ = σ y⁻¹ * (y * y⁻¹) := by rw [mul_inv_cancel₀ hy0, mul_one]
      _ = -y⁻¹ := by rw [← mul_assoc, hm, neg_one_mul]
  refine ⟨p, y⁻¹, hp.1, KneserThree.mem_alternatingSubspace_of_neg σ (mul_invOf_self _) hq,
    hp0, inv_ne_zero hy0, ?_⟩
  rw [← hpy, mul_assoc, mul_inv_cancel₀ hy0, mul_one]

/-- Given a factor of the desired Gram norm represented by the quaternion norm,
  construct a rank-three skew Gram matrix with the prescribed first entry. -/
def QuaternionicRankThreeNormModelStatement : Prop :=
  ∀ (F D : Type u) [Field F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] [Invertible (2 : F)]
    (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
    (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (c a : D), c ∈ τ.alternatingSubspace → c ≠ 0 → a ≠ 0 →
    ∃ d e : D, let H := Matrix.diagonal ![c, d, e]
      τ.IsAntihermitian H ∧ IsUnit H ∧ reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) =
        reducedNorm F D F (1 ⊗ₜ[F] c) * reducedNorm F D F (1 ⊗ₜ[F] a)

/-- Factor the reduced-norm representative into pure quaternions and add them
  as the two remaining diagonal entries. -/
theorem quaternionicRankThreeNormModel : QuaternionicRankThreeNormModelStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ c a hc hc0 ha
  obtain ⟨d, e, hd, he, hd0, he0, hde⟩ := τ.exists_mul_of_alternating hdim
    (σ.finrank_quaternionConjugation_alternating hdim hsym) a ha
  let v : Fin 3 → D := ![c, d, e]
  let H := Matrix.diagonal v
  have hv (i : Fin 3) : v i ∈ τ.alternatingSubspace := by
    fin_cases i
    · exact hc
    · exact hd
    · exact he
  have hv0 (i : Fin 3) : v i ≠ 0 := by
    fin_cases i
    · exact hc0
    · exact hd0
    · exact he0
  refine ⟨d, e, ?_, ?_, ?_⟩
  · change τ.IsAntihermitian H
    constructor
    · ext i j
      simp only [FirstKindInvolution.matrix_apply, Matrix.neg_apply, H, Matrix.diagonal_apply]
      by_cases h : i = j
      · subst j
        simp only [ite_true]
        obtain ⟨b, hb⟩ := τ.mem_alternatingSubspace.mp (hv i)
        rw [← hb, τ.map_sub, τ.apply_apply, neg_sub]
      · rw [ite_eq_right h, ite_eq_right (Ne.symm h), τ.map_zero, neg_zero]
    · intro i
      simpa only [H, Matrix.diagonal_apply_eq] using hv i
  · exact (Pi.isUnit_iff.mpr (fun i => isUnit_iff_ne_zero.mpr (hv0 i))).map (Matrix.diagonalRingHom (Fin 3) D)
  · change reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) = _
    let M := Matrix.diagonal (fun i => (1 : F) ⊗ₜ[F] v i)
    have hM : coefficientEquiv F D F ((1 : F) ⊗ₜ[F] H) = M := by
      ext i j
      rw [coefficientEquiv_tmul]
      by_cases hij : i = j
      · subst j
        simp [H, M]
      · simp [H, M, Matrix.diagonal_apply_ne _ hij]
    have hN : reducedNorm F (Matrix (Fin 3) (Fin 3) D) F (1 ⊗ₜ[F] H) = matrixReducedNorm F M := by
      change _ = reducedNorm F (Matrix (Fin 3) (Fin 3) D) F ((coefficientEquiv F D F).symm M)
      rw [← hM, AlgEquiv.symm_apply_apply]
    rw [hN, show M = Matrix.diagonal (fun i => (1 : F) ⊗ₜ[F] v i) from rfl,
      matrixReducedNorm_diagonal, Fin.prod_univ_three]
    change reducedNorm F D F (1 ⊗ₜ[F] c) * reducedNorm F D F (1 ⊗ₜ[F] d) *
      reducedNorm F D F (1 ⊗ₜ[F] e) = _
    rw [mul_assoc, ← _root_.map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, hde]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution
