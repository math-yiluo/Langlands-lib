import Langlands.GroupScheme.CoalgebraUnipotence.Quotient
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.Data.Nat.Find

noncomputable section

open Coalgebra TensorProduct
open Langlands.GroupScheme.AffineLinearEmbedding

namespace Langlands.GroupScheme.CoalgebraUnipotence

variable {k : Type*} [Field k] {B : Type*} [Ring B] [Bialgebra k B]

theorem eq_counit_smul_one_of_reduced_annihilation {b : B}
    (hb : ∀ f : Module.Dual k B, f 1 = 0 → f b = 0) :
    b = counit (R := k) b • (1 : B) := by
  apply sub_eq_zero.mp
  apply (Module.forall_dual_apply_eq_zero_iff k _).mp
  intro g
  have h := hb (g - g 1 • counit (R := k)) (by simp)
  simpa [map_sub, map_smul, mul_comm] using h

/-- The coefficient vector of a vector in a matrix corepresentation. -/
def coefficientVector {n : ℕ} (a : Matrix (Fin n) (Fin n) B)
    (v : Fin n → k) (i : Fin n) : B :=
  ∑ j, v j • a i j

theorem counit_coefficientVector {n : ℕ} {a : Matrix (Fin n) (Fin n) B}
    (ha : IsCoefficientMatrix (k := k) a) (v : Fin n → k) (i : Fin n) :
    counit (R := k) (coefficientVector a v i) = v i := by
  classical
  simp [coefficientVector, map_sum, ha.2, Matrix.one_apply]

theorem rightAct_coefficientVector {n : ℕ} {a : Matrix (Fin n) (Fin n) B}
    (ha : IsCoefficientMatrix (k := k) a) (v : Fin n → k) (f : Module.Dual k B)
    (i : Fin n) :
    rightAct f (coefficientVector a v i) =
      coefficientVector a (fun j => f (coefficientVector a v j)) i := by
  classical
  have hact : ∀ i j, rightAct f (a i j) = ∑ l, f (a l j) • a i l := by
    intro i j
    simp [rightAct_apply, ha.1 i j]
  simp only [coefficientVector, map_sum, map_smul, hact, Finset.smul_sum,
    Finset.sum_smul, smul_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  apply Finset.sum_congr rfl
  intro j _
  simp [smul_eq_mul]

theorem isMatrixUnipotent_of_isLocallyConilpotent
    (hB : IsLocallyConilpotent k B) : IsMatrixUnipotent k B := by
  classical
  intro n hn a ha
  let P : ℕ → Prop := fun m =>
    ∃ v : Fin n → k, v ≠ 0 ∧ ∀ i, coefficientVector a v i ∈ reducedLevel k B m
  have hex : ∃ m, P m := by
    let v : Fin n → k := fun _ => 1
    have hv : v ≠ 0 := by
      intro h
      exact one_ne_zero (congrFun h ⟨0, hn⟩)
    choose d hd using fun i => hB (coefficientVector a v i)
    refine ⟨Finset.univ.sup d, v, hv, fun i => ?_⟩
    exact reducedLevel_mono (Finset.le_sup (Finset.mem_univ i)) (hd i)
  obtain ⟨v, hv, hlevel⟩ := Nat.find_spec hex
  have hpos : Nat.find hex ≠ 0 := by
    intro hm
    apply hv
    funext i
    have hi : coefficientVector a v i = 0 := by
      exact (mem_reducedLevel_zero _).mp (hm ▸ hlevel i)
    have := congrArg (counit (R := k)) hi
    simpa [counit_coefficientVector ha] using this
  obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hpos
  have hlevel' : ∀ i, coefficientVector a v i ∈ reducedLevel k B (m + 1) := by
    simpa only [hm] using hlevel
  have hkill : ∀ f : Module.Dual k B, f 1 = 0 →
      (fun j => f (coefficientVector a v j)) = 0 := by
    intro f hf
    by_contra hne
    have hw : P m := by
      refine ⟨_, hne, fun i => ?_⟩
      rw [← rightAct_coefficientVector ha]
      exact (mem_reducedLevel_succ m _).mp (hlevel' i) f hf
    have hle := Nat.find_min' hex hw
    omega
  refine ⟨v, hv, fun i => ?_⟩
  change coefficientVector a v i = v i • (1 : B)
  rw [← counit_coefficientVector ha v i]
  apply eq_counit_smul_one_of_reduced_annihilation
  intro f hf
  exact congrFun (hkill f hf) i

end Langlands.GroupScheme.CoalgebraUnipotence
