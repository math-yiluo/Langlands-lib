import Langlands.GroupScheme.Examples.QuasiSplitUnitaryDynamic

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry Algebra
open scoped TensorProduct CategoryTheory.MonObj

namespace Langlands.GroupScheme.QuasiSplitUnitary

variable {F E : Type u} [Field F] [Field E] [Algebra F E]
  [IsQuadraticExtension F E]
attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {κ : Type u} [Fintype κ]
  (b : Module.Basis κ F (Matrix (Fin 2) (Fin 2) E)) (c : E ≃ₐ[F] E)

/-- The upper unipotent functor is the pointwise image of the trace-zero root map. -/
theorem upperUnipotent_eq_range (T : Over (Spec (CommRingCat.of F))) :
    (upperUnipotent b c).carrier T = (upperRootPoints b c T).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨h10, h00, h11⟩ := (mem_upperUnipotent b c).mp hg
    have hM : (matrixCoordinates b c T g : Matrix (Fin 2) (Fin 2) _) =
        !![1, matrixCoordinates b c T g 0 1; 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h10, h00, h11]
    have hu : (pointsEquiv b c T g).val ∈ matrixPoints
        ((algΓ (CommRingCat.of F)).obj T).unop c := (pointsEquiv b c T g).property
    dsimp only [matrixPoints] at hu
    rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff] at hu
    change (matrixCoordinates b c T g).val *
      adjoint (scalarConjugation _ c) (matrixCoordinates b c T g).val = 1 at hu
    have ht := congrArg (fun M => M 0 1) hu
    rw [hM] at ht
    have hx : matrixCoordinates b c T g 0 1 +
        scalarConjugation _ c (matrixCoordinates b c T g 0 1) = 0 := by
      simpa [adjoint, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using ht
    refine ⟨Multiplicative.ofAdd ⟨matrixCoordinates b c T g 0 1, hx⟩, ?_⟩
    apply (pointsEquiv b c T).injective
    rw [pointsEquiv_upperRootPoints]
    apply Subtype.ext
    apply Units.ext
    exact hM.symm
  · rintro ⟨x, rfl⟩
    rw [mem_upperUnipotent]
    have h : matrixCoordinates b c T (upperRootPoints b c T x) = (upperRoot _ c x).val := by
      change (pointsEquiv b c T (upperRootPoints b c T x)).val = _
      rw [pointsEquiv_upperRootPoints]
    rw [h]
    simp [upperRoot, upperRootMatrix]

/-- The lower unipotent functor is the pointwise image of the trace-zero root map. -/
theorem lowerUnipotent_eq_range (T : Over (Spec (CommRingCat.of F))) :
    (lowerUnipotent b c).carrier T = (lowerRootPoints b c T).range := by
  apply Subgroup.ext
  intro g
  constructor
  · intro hg
    obtain ⟨h01, h00, h11⟩ := (mem_lowerUnipotent b c).mp hg
    have hM : (matrixCoordinates b c T g : Matrix (Fin 2) (Fin 2) _) =
        !![1, 0; matrixCoordinates b c T g 1 0, 1] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [h01, h00, h11]
    have hu : (pointsEquiv b c T g).val ∈ matrixPoints
        ((algΓ (CommRingCat.of F)).obj T).unop c := (pointsEquiv b c T g).property
    dsimp only [matrixPoints] at hu
    rw [Langlands.Shimura.AlgebraInvolution.mem_unitary_iff] at hu
    change (matrixCoordinates b c T g).val *
      adjoint (scalarConjugation _ c) (matrixCoordinates b c T g).val = 1 at hu
    have ht := congrArg (fun M => M 1 0) hu
    rw [hM] at ht
    have hx : matrixCoordinates b c T g 1 0 +
        scalarConjugation _ c (matrixCoordinates b c T g 1 0) = 0 := by
      simpa [adjoint, Matrix.mul_apply, Fin.sum_univ_two, add_comm] using ht
    refine ⟨Multiplicative.ofAdd ⟨matrixCoordinates b c T g 1 0, hx⟩, ?_⟩
    apply (pointsEquiv b c T).injective
    rw [pointsEquiv_lowerRootPoints]
    apply Subtype.ext
    apply Units.ext
    exact hM.symm
  · rintro ⟨x, rfl⟩
    rw [mem_lowerUnipotent]
    have h : matrixCoordinates b c T (lowerRootPoints b c T x) = (lowerRoot _ c x).val := by
      change (pointsEquiv b c T (lowerRootPoints b c T x)).val = _
      rw [pointsEquiv_lowerRootPoints]
    rw [h]
    simp [lowerRoot, lowerRootMatrix]

end Langlands.GroupScheme.QuasiSplitUnitary
