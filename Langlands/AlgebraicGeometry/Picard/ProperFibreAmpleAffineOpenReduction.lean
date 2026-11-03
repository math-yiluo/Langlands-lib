import Langlands.AlgebraicGeometry.Picard.ProperFibreAmpleAffineOpenReductionStatement
import Langlands.AlgebraicGeometry.Picard.AmpleFiniteAffineOpen

/-! # The proper-family affine-neighbourhood reduction -/

universe u

open CategoryTheory AlgebraicGeometry

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard

/-- Spreading the specified ample bundle reduces the proper-family statement
to affine neighbourhoods of finite sets on an ample scheme. -/
theorem properFibreAmpleAffineOpen_of_spreading
    (hspread : ProperFibreAmpleSpreadingStatement.{u}) :
    ProperFibreAmpleAffineOpenStatement.{u} := by
  classical
  intro X S _ f _ L s hL E hE
  obtain ⟨V, hsV, _hV, hLV⟩ := hspread X S f L s hL
  let U : X.Opens := f ⁻¹ᵁ V
  have hEU : (E : Set X) ⊆ U := by
    intro x hx
    change f x ∈ V
    rw [hE x hx]
    exact hsV
  have hfinite : (U.ι ⁻¹' (E : Set X)).Finite :=
    E.finite_toSet.preimage U.ι.isOpenEmbedding.injective.injOn
  obtain ⟨W, hW, hEW, _⟩ := exists_isAffineOpen_of_finite_of_ample
    U.toScheme ((LineBundle.pullback U.ι).obj L) hLV
    (U.ι ⁻¹' (E : Set X)) ⊤ hfinite (by simp)
  refine ⟨U.ι ''ᵁ W, hW.image_of_isOpenImmersion U.ι, ?_⟩
  intro x hx
  exact ⟨⟨x, hEU hx⟩, hEW hx, rfl⟩

/-- The conditional reduction packaged as its named proposition. -/
theorem properFibreAmpleAffineOpenReduction :
    ProperFibreAmpleAffineOpenReductionStatement.{u} :=
  properFibreAmpleAffineOpen_of_spreading

end Langlands.AlgebraicGeometry.Picard
