import Langlands.GroupScheme.Torus.MultiplicativeTypePointedMapReduction
import Langlands.GroupScheme.Torus.UnitsProductDecomposition

/-! # Pointed maps to groups of multiplicative type -/

universe u

namespace Langlands.GroupScheme

/-- A morphism from a connected group variety to a group of multiplicative type
that preserves the identity is a homomorphism of group schemes. -/
theorem multiplicativeTypePointedMap : MultiplicativeTypePointedMapStatement.{u} :=
  multiplicativeTypePointedMap_of_unitsProductDecomposition.{u}
    unitsProductDecomposition.{u}

end Langlands.GroupScheme
