import Langlands.GroupScheme.Rational.Statement
import Langlands.GroupScheme.Reductive.RootDatum

/-! # Statement: the rational structure of `GL_n` -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **The rational structure of `GL_n`.** For every field `k` and every finite type `n` with
decidable equality, the diagonal torus `D_n ⟶ GL_n` over `k` is a maximal split torus, its
relative roots are the characters `eᵢ - eⱼ` with `i ≠ j`, it has a relative root system in the
sense of `HasRelativeRootSystem`, and the dynamic Levi subgroup of every generic cocharacter is
the torus centralizer. -/
def GeneralLinearRationalStatement : Prop :=
  ∀ (k : Type u) [Field k] (n : Type) [Fintype n] [DecidableEq n],
    IsMaximalSplitTorus (GeneralLinear.diagonalTorus n (CommRingCat.of k)) ∧
    relativeRoots (GeneralLinear.diagonalTorus n (CommRingCat.of k)) =
      {χ | ∃ i j : n, i ≠ j ∧ splitTorus.characterLatticeEquiv k (ULift.{u} n) χ =
        Pi.single (ULift.up i) 1 - Pi.single (ULift.up j) 1} ∧
    HasRelativeRootSystem (GeneralLinear.diagonalTorus n (CommRingCat.of k)) ∧
    ∀ ν : cocharacterLattice
        (splitTorus.commGroupScheme (Spec (CommRingCat.of k)) (ULift.{u} n)),
      IsGenericCocharacter (GeneralLinear.diagonalTorus n (CommRingCat.of k)) ν →
        Dynamic.centralizer
            (CommGroupScheme.groupHom ν ≫ GeneralLinear.diagonalTorus n (CommRingCat.of k)) =
          torusCentralizer (GeneralLinear.diagonalTorus n (CommRingCat.of k))

end Langlands.GroupScheme
