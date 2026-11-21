import Langlands.Algebra.BrauerGroup
import Langlands.Algebra.CentralSimple.UnitaryDivisionSplitting

/-! # Split and division quaternion coefficient algebras -/

noncomputable section

open scoped TensorProduct

universe u

namespace Langlands.GroupScheme.Quaternionic

/-- A scalar extension of a central quaternion division algebra is either a domain
  or a two-by-two matrix algebra. -/
def QuaternionCoefficientDichotomyStatement : Prop :=
  ∀ (F D R : Type u) [Field F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] [Field R] [Algebra F R],
    Module.finrank F D = 4 →
      IsDomain (R ⊗[F] D) ∨ Nonempty (R ⊗[F] D ≃ₐ[R] Matrix (Fin 2) (Fin 2) R)

theorem quaternionCoefficientDichotomy : QuaternionCoefficientDichotomyStatement.{u} := by
  intro F D R _ _ _ _ _ _ _ hD
  let A := R ⊗[F] D
  let : IsSimpleRing A := Langlands.CentralSimple.isSimpleRing_baseChange F D R
  let : IsArtinianRing A := IsArtinianRing.of_finite R A
  obtain ⟨n, hn, E, _, _, _, ⟨e⟩⟩ := IsSimpleRing.exists_algEquiv_matrix_divisionRing_finite R A
  have hd : Module.finrank R A = 4 := Module.finrank_baseChange.trans hD
  rw [e.toLinearEquiv.finrank_eq, Module.finrank_matrix, Fintype.card_fin] at hd
  have hpos : 1 ≤ Module.finrank R E := Module.finrank_pos
  have hnn : n * n ≤ 4 := by
    calc n * n = n * n * 1 := by rw [mul_one]
      _ ≤ n * n * Module.finrank R E := Nat.mul_le_mul_left _ hpos
      _ = 4 := hd
  have hn2 : n ≤ 2 := (Nat.le_sqrt.mpr hnn).trans_eq (Nat.sqrt_eq 2)
  have hn1 : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  rcases (show n = 1 ∨ n = 2 by omega) with rfl | rfl
  · exact Or.inl ((e.trans (Langlands.Brauer.matrixOneEquiv E)).toMulEquiv.isDomain E)
  · have hE : Module.finrank R E = 1 := by omega
    let j := Langlands.Algebra.CentralSimple.algEquivOfFinrankEqOne hE
    exact Or.inr ⟨e.trans j.symm.mapMatrix⟩

end Langlands.GroupScheme.Quaternionic
