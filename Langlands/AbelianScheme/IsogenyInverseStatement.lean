import Langlands.AbelianScheme.GroupScheme
import Langlands.AbelianScheme.Isogeny
import Langlands.AbelianScheme.Kernel
import Langlands.AbelianScheme.Multiplication
import Langlands.CategoryTheory.Rationalization

/-! # Rational invertibility with a uniform kernel annihilator -/

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.CommGroupScheme

universe u

/-- An isogeny whose scheme kernel is killed by one nonzero integer becomes
an isomorphism in the rationalization of commutative group schemes. -/
def IsogenyInverseStatement : Prop :=
  ∀ (S : Scheme.{u}) (G H : CommGroupScheme S) (f : G ⟶ H),
    GroupScheme.IsIsogeny (groupHom f) →
    (∃ n : ℤ, n ≠ 0 ∧
      GroupScheme.multiplication (GroupScheme.kernel (groupHom f)) n = 1) →
    IsIso ((Rationalization.inclusion (C := CommGroupScheme S)).map f)

end Langlands.CommGroupScheme
