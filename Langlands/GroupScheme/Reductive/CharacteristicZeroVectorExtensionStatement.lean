import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Rational.RootSubgroupStructureStatement
import Langlands.AbelianScheme.Kernel

/-! # The vector-kernel step in characteristic-zero Levi decomposition -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A faithfully flat affine extension of a connected reductive group by a
full vector kernel has a homomorphic section in characteristic zero. -/
def CharacteristicZeroReductiveVectorExtensionStatement : Prop :=
  ∀ (k : Type u) [Field k] [CharZero k]
    (E H : GroupScheme (Spec (CommRingCat.of k))) [IsAffineHom E.X.hom]
    (q : E ⟶ H) [Flat q.hom.hom.left] [Surjective q.hom.hom.left],
    IsConnectedReductive H →
      ∀ d : ℕ, RelativeRoot.IsVectorGroupOfDimension (kernel q) d →
        ∃ s : H ⟶ E, s ≫ q = 𝟙 H

end Langlands.GroupScheme
