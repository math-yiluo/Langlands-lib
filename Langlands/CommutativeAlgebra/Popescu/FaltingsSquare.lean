import Langlands.CommutativeAlgebra.Popescu.FaltingsRows

/-! # Naturality of the Jacobi–Zariski connecting map for a local map `A → A'` -/

universe u

namespace Langlands.CommutativeAlgebra.Popescu

namespace Faltings

open IsLocalRing

open scoped TensorProduct

variable {A A' : Type u} [CommRing A] [CommRing A'] [IsLocalRing A] [IsLocalRing A']
  [Algebra A A'] [IsLocalHom (algebraMap A A')]

theorem h1_map_square (x : Algebra.H1Cotangent A (ResidueField A)) :
    Algebra.H1Cotangent.map A A' (ResidueField A) (ResidueField A') x =
      Algebra.H1Cotangent.map A A' (ResidueField A') (ResidueField A')
        (Algebra.H1Cotangent.map A A (ResidueField A) (ResidueField A') x) := by
  simp only [Algebra.H1Cotangent.map]
  rw [← Algebra.Extension.H1Cotangent.map_comp_apply]
  exact LinearMap.congr_fun (Algebra.Extension.H1Cotangent.map_eq _ _) x

/-- `δ_{A'}(H₁(map)(x)) = (K' ⊗_A Ω_A → K' ⊗_{A'} Ω_{A'})(1 ⊗ δ_A x)`. -/
theorem δ_square (x : Algebra.H1Cotangent A (ResidueField A)) :
    Algebra.H1Cotangent.δ ℤ A' (ResidueField A')
        (Algebra.H1Cotangent.map A A' (ResidueField A) (ResidueField A') x) =
      baseMap ℤ A A' (ResidueField A')
        (TensorProduct.AlgebraTensorModule.cancelBaseChange A (ResidueField A) (ResidueField A')
          (ResidueField A') Ω[A⁄ℤ]
          ((1 : ResidueField A') ⊗ₜ[ResidueField A] Algebra.H1Cotangent.δ ℤ A (ResidueField A) x)) := by
  rw [h1_map_square, δ_map_base, FieldH1.δ_map]

end Faltings

end Langlands.CommutativeAlgebra.Popescu
