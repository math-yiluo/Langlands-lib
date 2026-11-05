import Langlands.GroupScheme.Torus.Geometry
import Langlands.GroupScheme.Reductive.SemisimpleFieldReflectionProof

/-! # Connected reductivity of a torus from a splitting field -/

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]

/-- A torus is connected reductive, by splitting and field-extension reflection. -/
theorem IsTorus.isConnectedReductive_of_fieldSplitting
    {T : GroupScheme (Spec (CommRingCat.of k))} (hT : IsTorus T) :
    IsConnectedReductive T := by
  obtain ⟨K, hK, aK, hs⟩ := hT
  exact hs.isConnectedReductive.of_fieldExtension

end Langlands.GroupScheme
