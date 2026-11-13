import Langlands.GroupScheme.SymplecticInnerForm.MatrixSpan
import Langlands.GroupScheme.SpecialLinearInnerForm.ConjugationDescent

/-! # Descending algebra maps from their values on symplectic matrices -/

noncomputable section

namespace Langlands.GroupScheme.SymplecticInnerForm

variable {l : Type} [Fintype l] [DecidableEq l]
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

variable (φ ψ : Matrix (l ⊕ l) (l ⊕ l) R →ₐ[R] Matrix (l ⊕ l) (l ⊕ l) B)
    (hSp : ∀ g : Matrix.symplecticGroup l R, ∃ y, φ y = ψ g)

include hSp

/-- If the values on symplectic matrices lie in a coefficient image, then all
matrix values lie in that image. -/
theorem image_of_symplectic (X : Matrix (l ⊕ l) (l ⊕ l) R) : ∃ y, φ y = ψ X := by
  let P : Submodule R (Matrix (l ⊕ l) (l ⊕ l) R) :=
    φ.toLinearMap.range.comap ψ.toLinearMap
  have htop : (⊤ : Submodule R (Matrix (l ⊕ l) (l ⊕ l) R)) ≤ P := by
    rw [← span_symplectic]
    apply Submodule.span_le.mpr
    rintro _ ⟨g, rfl⟩
    exact hSp g
  exact htop (Submodule.mem_top : X ∈ (⊤ : Submodule R (Matrix (l ⊕ l) (l ⊕ l) R)))

variable (hφ : Function.Injective φ)

/-- Descend an algebra map through an injective coefficient map using its values
on symplectic matrices. -/
def descendMatrixAlgHom :
    Matrix (l ⊕ l) (l ⊕ l) R →ₐ[R] Matrix (l ⊕ l) (l ⊕ l) R :=
  SpecialLinearInnerForm.descendMatrixAlgHom φ ψ
    (fun g => image_of_symplectic φ ψ hSp g) hφ

/-- The descended algebra map recovers the supplied map after coefficient change. -/
theorem map_descendMatrixAlgHom (X : Matrix (l ⊕ l) (l ⊕ l) R) :
    φ (descendMatrixAlgHom φ ψ hSp hφ X) = ψ X :=
  SpecialLinearInnerForm.map_descendMatrixAlgHom φ ψ
    (fun g => image_of_symplectic φ ψ hSp g) hφ X

end Langlands.GroupScheme.SymplecticInnerForm
