import Langlands.GroupScheme.Examples.QuasiSplitUnitaryLevi
import Langlands.GroupScheme.SubgroupFunctor

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]

section Matrices
variable (R : Type u) [CommRing R] [Algebra F R]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

/-- The first diagonal entry of a lower triangular unitary matrix, as a tensor unit. -/
def firstDiagonalUnit (c : E ≃ₐ[F] E) (g : matrixPoints R c)
    (h01 : (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 1 = 0) : (E ⊗[F] R)ˣ := by
  have hg := g.property
  dsimp only [matrixPoints] at hg
  rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff] at hg
  have h00 := congrArg (fun M : Matrix (Fin 2) (Fin 2) (E ⊗[F] R) => M 0 0) hg
  simp only [matrixInvolution_apply, adjoint, Matrix.mul_apply, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    h01, zero_mul, add_zero, Matrix.one_apply_eq] at h00
  exact
    { val := (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 0
      inv := scalarConjugation R c
        ((g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 1 1)
      val_inv := h00
      inv_val := by rw [mul_comm]; exact h00 }

/-- The diagonal unitary matrices are exactly the images of tensor units. -/
theorem leviDiagonalUnitary_range_iff (c : E ≃ₐ[F] E) (g : matrixPoints R c) :
    (∃ a, leviDiagonalUnitary R c a = g) ↔
      (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 0 1 = 0 ∧
      (g.val : Matrix (Fin 2) (Fin 2) (E ⊗[F] R)) 1 0 = 0 := by
  constructor
  · rintro ⟨a, rfl⟩
    simp [leviDiagonalUnitary_val]
  · rintro ⟨h01, h10⟩
    let a := firstDiagonalUnit R c g h01
    refine ⟨a, ?_⟩
    apply Subtype.ext
    apply Units.ext
    rw [leviDiagonalUnitary_val]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [a, firstDiagonalUnit, h01, h10]
    exact scalarConjugation_involutive R c _

end Matrices

section Schemes
attribute [local instance] Algebra.TensorProduct.rightAlgebra
variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- Postcomposition with the Levi homomorphism is injective on every test scheme. -/
theorem leviHom_points_injective (T : Over (Spec (CommRingCat.of F))) :
    Function.Injective (fun a : T ⟶ (WeilGm.groupScheme (CommRingCat.of F) E).X =>
      a ≫ (leviHom b c).hom.hom) := by
  intro a d h
  apply (WeilGm.pointsEquiv (CommRingCat.of F) E T).injective
  apply leviDiagonalUnitary_injective _ c
  simpa only [pointsEquiv_leviHom] using congrArg (pointsEquiv b c T) h

/-- The Levi homomorphism is a monomorphism over the field. -/
instance leviHom_mono : Mono (leviHom b c).hom.hom where
  right_cancellation := fun {T} _ _ h => leviHom_points_injective b c T h

/-- On all test schemes, the Levi homomorphism has exactly the diagonal unitary points. -/
theorem range_leviHom : SubgroupFunctor.range (leviHom b c) = diagonal b c := by
  ext T x
  rw [SubgroupFunctor.mem_range, mem_diagonal]
  constructor
  · rintro ⟨a, rfl⟩
    change ((pointsEquiv b c T (a ≫ (leviHom b c).hom.hom)).val :
      Matrix (Fin 2) (Fin 2) (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)) 0 1 = 0 ∧
      ((pointsEquiv b c T (a ≫ (leviHom b c).hom.hom)).val :
      Matrix (Fin 2) (Fin 2) (E ⊗[F] ((algΓ (CommRingCat.of F)).obj T).unop)) 1 0 = 0
    simpa only [pointsEquiv_leviHom] using
      (leviDiagonalUnitary_range_iff _ c _).1 ⟨_, rfl⟩
  · intro hx
    obtain ⟨a, ha⟩ := (leviDiagonalUnitary_range_iff _ c (pointsEquiv b c T x)).2 hx
    refine ⟨(WeilGm.pointsEquiv (CommRingCat.of F) E T).symm a, ?_⟩
    apply (pointsEquiv b c T).injective
    rw [pointsEquiv_leviHom, MulEquiv.apply_symm_apply]
    exact ha

/-- The tensor-unit Weil restriction represents the diagonal unitary subgroup functor. -/
theorem diagonal_isRepresentedBy_leviHom : (diagonal b c).IsRepresentedBy (leviHom b c) :=
  ⟨inferInstance, range_leviHom b c⟩

end Schemes
end Langlands.GroupScheme.QuasiSplitUnitary
