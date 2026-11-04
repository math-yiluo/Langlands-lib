import Langlands.GroupScheme.UnipotentMatrixCriterion.Statement
import Langlands.GroupScheme.UnipotentMatrixCriterion.Coordinates

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.GroupScheme.UnipotentMatrixCriterion

theorem corepresentedMatrixUnipotence : CorepresentedMatrixUnipotenceStatement.{u} := by
  intro k _ F B e
  let := AffineLinearEmbedding.bialgebra e
  constructor
  · intro h N hN a ha
    let : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
    let ρ : MatrixRepresentation (Corepresented.groupScheme F e) (Fin N) :=
      Corepresented.groupSchemeMap e (GeneralLinear.corepresentableBy (Fin N) (CommRingCat.of k))
        (Corepresented.LinearEmbedding.toGL e a ha.1 ha.2)
    obtain ⟨v, hv, hfix⟩ := h (Fin N) ρ
    refine ⟨v, hv, ?_⟩
    have hf := (isFixedVector_iff e ρ v).mp hfix
    have hc : coefficientMatrix e ρ = a := coefficientMatrix_toGL e a ha.1 ha.2
    rwa [hc] at hf
  · intro h n _ _ _ ρ
    let f : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm
    let a : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) B :=
      fun i j => coefficientMatrix e ρ (f i) (f j)
    have ha : CoalgebraUnipotence.IsCoefficientMatrix (k := k) a := by
      constructor
      · intro i j
        change AffineLinearEmbedding.comul e (coefficientMatrix e ρ (f i) (f j)) =
          ∑ l, coefficientMatrix e ρ (f i) (f l) ⊗ₜ[k] coefficientMatrix e ρ (f l) (f j)
        rw [coefficientMatrix_comul]
        exact (f.sum_comp fun l =>
          coefficientMatrix e ρ (f i) l ⊗ₜ[k] coefficientMatrix e ρ l (f j)).symm
      · intro i j
        change AffineLinearEmbedding.counit e (coefficientMatrix e ρ (f i) (f j)) =
          (1 : Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) k) i j
        rw [coefficientMatrix_counit]
        simp only [Matrix.one_apply, f.injective.eq_iff]
    obtain ⟨v, hv, hfix⟩ := h (Fintype.card n) Fintype.card_pos a ha
    refine ⟨fun i => v (f.symm i), ?_, (isFixedVector_iff e ρ _).mpr ?_⟩
    · intro hz
      apply hv
      funext i
      have hi := congrFun hz (f i)
      simpa only [Equiv.symm_apply_apply, Pi.zero_apply] using hi
    · intro i
      have hi := hfix (f.symm i)
      change (∑ j, v j • coefficientMatrix e ρ (f (f.symm i)) (f j)) =
        v (f.symm i) • (1 : B) at hi
      rw [Equiv.apply_symm_apply] at hi
      calc
        ∑ j, v (f.symm j) • coefficientMatrix e ρ i j =
            ∑ j, v j • coefficientMatrix e ρ i (f j) := by
          simpa only [Equiv.symm_apply_apply] using
            (f.sum_comp fun j => v (f.symm j) • coefficientMatrix e ρ i j).symm
        _ = _ := hi

end Langlands.GroupScheme.UnipotentMatrixCriterion
