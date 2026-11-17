import Langlands.AlgebraicGeometry.Picard.EquivariantLineBundle
import Langlands.AlgebraicGeometry.Modules.Tensor

/-! # Equivariant structures on tensor powers of equivariant line bundles -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

/-- Every tensor power of the chart bundle of an actual equivariant line bundle is,
up to an isomorphism of module sheaves, the chart bundle of an actual equivariant
line bundle on the same étale equivalence relation. -/
def EquivariantLineBundleTensorPowStatement : Prop :=
  ∀ (E : EtaleEquivalenceRelation.{u}) (B : EquivariantLineBundle E) (n : ℕ),
    ∃ B' : EquivariantLineBundle E,
      Nonempty (B'.bundle.obj ≅ Langlands.Scheme.Modules.tensorPow B.bundle.obj n)

end Langlands.AlgebraicGeometry.Picard
