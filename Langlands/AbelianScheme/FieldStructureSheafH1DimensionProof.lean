import Langlands.AbelianScheme.FieldStructureSheafH1DimensionStatement
import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundProof
import Langlands.AbelianScheme.FieldH1LowerBound

/-! # The first structure-sheaf cohomology of an abelian variety has dimension `g` -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over every field, the first structure-sheaf cohomology of an abelian variety of relative
dimension `g` is finite-dimensional of dimension exactly `g`. -/
theorem fieldStructureSheafH1Dimension : FieldStructureSheafH1DimensionStatement.{u} := by
  intro k _ A g hg H
  obtain ⟨hfin, hle⟩ := fieldStructureSheafH1DimensionBound k A g hg
  exact ⟨hfin, le_antisymm hle (FieldH1LowerBound.le_finrank A g hg)⟩

end Langlands.AbelianScheme
