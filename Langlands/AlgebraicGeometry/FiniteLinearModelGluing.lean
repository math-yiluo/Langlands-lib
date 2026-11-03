import Langlands.AlgebraicGeometry.FiniteLinearModels
import Langlands.AlgebraicGeometry.AlgebraicSpace.LocalRepresentationProperties

/-! # Global representations from local finite linear models -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FiniteLinearEquations.HasLocalModels

variable {B : Scheme.{u}} {F : AlgebraicSpace.Presheaf B}

/-- An fppf sheaf with local finite homogeneous linear models has an actual
scheme representative with affine locally finitely presented structure map. -/
theorem exists_affine_representation (hModel : HasLocalModels F)
    (hSheaf : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology B) F) :
    ∃ V : Over B, Nonempty ((AlgebraicSpace.schemeYoneda B).obj V ≅ F) ∧
      IsAffineHom V.hom ∧ LocallyOfFinitePresentation V.hom := by
  obtain ⟨I, R, j, hj, hcover, hrep⟩ := hModel.exists_local_representations
  choose H he hAffine hFP using hrep
  let 𝒰 : Scheme.OpenCover.{u} B :=
    { I₀ := I
      X := fun i ↦ Spec (R i)
      f := j
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨?_, hj⟩
        intro b
        obtain ⟨i, x, hx⟩ := hcover b
        exact ⟨i, x, hx⟩ }
  exact AlgebraicSpace.LocalRepresentation.exists_affine_representation
    hSheaf 𝒰 H (fun i ↦ (he i).some) hAffine hFP

/-- The representative, its full-slice natural comparison, and both morphism
properties as actual data, chosen from the proved existence theorem. -/
def representation (hModel : HasLocalModels F)
    (hSheaf : Presheaf.IsSheaf (AlgebraicSpace.fppfTopology B) F) :
    Σ V : Over B, { _e : (AlgebraicSpace.schemeYoneda B).obj V ≅ F //
      IsAffineHom V.hom ∧ LocallyOfFinitePresentation V.hom } :=
  let h := exists_affine_representation hModel hSheaf
  ⟨h.choose, h.choose_spec.1.some, h.choose_spec.2⟩

end Langlands.AlgebraicGeometry.FiniteLinearEquations.HasLocalModels
