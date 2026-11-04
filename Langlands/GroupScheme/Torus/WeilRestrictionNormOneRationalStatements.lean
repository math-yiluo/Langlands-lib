import Langlands.GroupScheme.Torus.WeilRestrictionNormOne
import Langlands.GroupScheme.Torus.Lattice

/-! # Ground-field characters and cocharacters of the norm-one group -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.WeilGm

variable (k K : Type u) [Field k] [Field K] [Algebra k K]
  [FiniteDimensional k K]

/-- Every actual ground-field character of the norm-one group is trivial. -/
def normOneRationalCharacterVanishingStatement : Prop :=
  ∀ χ : characterLattice (normOneCommGroupScheme (CommRingCat.of k) K), χ = 0

/-- Every actual ground-field cocharacter of the norm-one group is trivial. -/
def normOneRationalCocharacterVanishingStatement : Prop :=
  ∀ ν : cocharacterLattice (normOneCommGroupScheme (CommRingCat.of k) K), ν = 0

/-- For a finite separable extension, both actual norm-one lattices over the
ground field vanish. -/
def normOneRationalLatticesStatement : Prop :=
  Algebra.IsSeparable k K →
    normOneRationalCharacterVanishingStatement k K ∧
    normOneRationalCocharacterVanishingStatement k K

end Langlands.GroupScheme.WeilGm
