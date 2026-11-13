import Langlands.AbelianScheme.FieldStructureSheafH1DimensionBoundStatement

/-! # Dimension of the first structure-sheaf cohomology of an abelian variety -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- Over every field, the actual first structure-sheaf cohomology of an abelian
variety of relative dimension `g` is finite-dimensional of dimension `g`.
This proposition does not assume a Picard parameter or a chosen dual. -/
def FieldStructureSheafH1DimensionStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Spec (CommRingCat.of k))) (g : ℕ),
    A.HasRelativeDimension g →
      let H := (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
        A.X.hom 1).obj (Langlands.Scheme.Modules.structureSheaf A.X.left)
      FiniteDimensional k H ∧ Module.finrank k H = g

end Langlands.AbelianScheme
