import Langlands.AbelianScheme.Basic
import Langlands.AlgebraicGeometry.Modules.DerivedSections
import Langlands.AlgebraicGeometry.Modules.Tensor
import Mathlib.LinearAlgebra.FiniteDimensional.Defs

/-! # The dimension bound for `H¹(A, 𝒪_A)` of an abelian scheme over a field -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

/-- For an abelian scheme `A` over `Spec k`, `k` an arbitrary field, whose smooth
structure morphism has a specified relative dimension `g`, the first cohomology
`H¹(A, 𝒪_A)` of the actual structure sheaf, computed as Library right-derived
`k`-module global sections, is finite-dimensional over `k` of dimension at most `g`. -/
def FieldStructureSheafH1DimensionBoundStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (A : AbelianScheme (Scheme.Spec.obj (Opposite.op (CommRingCat.of k))))
    (g : ℕ),
    A.HasRelativeDimension g →
      let H := (Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomology
        A.X.hom 1).obj (Langlands.Scheme.Modules.structureSheaf A.X.left)
      FiniteDimensional k H ∧ Module.finrank k H ≤ g

end Langlands.AbelianScheme
