import Langlands.Weil.Representation.Operations
import Mathlib.LinearAlgebra.TensorProduct.Matrix

/-! # Rank and determinant identities for representation operations -/

noncomputable section

open scoped TensorProduct

namespace Langlands

universe uK uG uV uU

section Field

variable {K : Type uK} [Field K]
variable {V : Type uV} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
variable {U : Type uU} [AddCommGroup U] [Module K U] [FiniteDimensional K U]

/-- The determinant of a tensor product of endomorphisms follows from the
Kronecker determinant formula in tensor-product bases. -/
theorem det_tensorProduct_map (A : Module.End K V) (B : Module.End K U) :
    LinearMap.det (TensorProduct.map A B) =
      LinearMap.det A ^ Module.finrank K U *
        LinearMap.det B ^ Module.finrank K V := by
  classical
  let bV := Module.finBasis K V
  let bU := Module.finBasis K U
  rw [← LinearMap.det_toMatrix (bV.tensorProduct bU), TensorProduct.toMatrix_map,
    Matrix.det_kronecker, LinearMap.det_toMatrix, LinearMap.det_toMatrix]
  simp only [Fintype.card_fin]

variable {G : Type uG} [Group G]

/-- Contragredience inverts the determinant character. -/
theorem det_representation_dual (ρ : Representation K G V) (g : G) :
    LinearMap.det (ρ.dual g) = (LinearMap.det (ρ g))⁻¹ := by
  change LinearMap.det (ρ g⁻¹).dualMap = _
  rw [LinearMap.det_dualMap]
  apply eq_inv_of_mul_eq_one_left
  rw [← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one]

omit [FiniteDimensional K V] in
/-- A scalar character twist contributes its value to the power of the finrank. -/
theorem det_twist (χ : G →* Kˣ) (ρ : Representation K G V) (g : G) :
    LinearMap.det (twist χ ρ g) =
      (χ g : K) ^ Module.finrank K V * LinearMap.det (ρ g) := by
  change LinearMap.det ((χ g : K) • ρ g) = _
  exact LinearMap.det_smul _ _

end Field

namespace Weil

/-- Rank and determinant identities for sums, tensors, duals and scalar twists. -/
theorem representationRankDeterminant :
    RepresentationRankDeterminant.{uG, uV, uU} := by
  intro G _ V _ _ _ U _ _ _ ρ σ
  refine ⟨Module.finrank_prod, Module.finrank_tensorProduct,
    Subspace.dual_finrank_eq, ?_, ?_⟩
  · intro g
    exact ⟨LinearMap.det_prodMap _ _,
      det_tensorProduct_map (ρ g) (σ g), det_representation_dual ρ g⟩
  · exact fun χ g => det_twist χ ρ g

end Weil

end Langlands
