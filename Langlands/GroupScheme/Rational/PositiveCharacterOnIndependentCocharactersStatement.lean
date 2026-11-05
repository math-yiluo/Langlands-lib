import Langlands.GroupScheme.Torus.Lattice
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-! # A positive character on independent cocharacters of a split torus -/

universe u v

open AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A finite integral-linearly-independent family of actual cocharacters of a
split torus admits one actual character whose pairing with every member is
strictly positive. -/
def PositiveCharacterOnIndependentCocharactersStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (T : CommGroupScheme (Spec (CommRingCat.of k))),
    IsSplitTorus T.toGrp →
    ∀ (I : Type v) [Finite I] (x : I → cocharacterLattice T),
      LinearIndependent ℤ x →
      ∃ α : characterLattice T, ∀ i, 0 < latticePairing T α (x i)

end Langlands.GroupScheme
