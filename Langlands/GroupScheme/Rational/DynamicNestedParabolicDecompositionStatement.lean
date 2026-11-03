import Langlands.GroupScheme.Dynamic.NestedParabolic

/-! # The all-test nested semistandard parabolic decomposition target -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Compatible nested dynamic parabolics in a connected reductive group have
the three nested Levi product decompositions on every test scheme. -/
def DynamicNestedParabolicDecompositionStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ χ ψ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
      Dynamic.IsCompatibleNestedPair χ ψ →
        Dynamic.NestedParabolicDecomposition χ ψ

end Langlands.GroupScheme
