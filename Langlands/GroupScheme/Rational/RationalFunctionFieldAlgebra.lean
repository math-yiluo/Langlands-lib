import Langlands.GroupScheme.Rational.MaximalTorusParameterDescent
import Langlands.GroupScheme.Torus.LatticeGalois

/-! # Rational function fields as algebras over the base field -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

variable (k : Type u) [Field k] (m : Type u)

/-- The function field of `𝔸(m; Spec k)` as a `k`-algebra, through the structure morphism of
`rationalFunctionFieldOver k m`. -/
@[reducible] def rationalFunctionFieldAlgebra :
    Algebra k (𝔸(m; Spec (CommRingCat.of k))).functionField :=
  (Spec.preimage (rationalFunctionFieldOver k m).hom).hom.toAlgebra

attribute [instance] rationalFunctionFieldAlgebra

/-- The `i`-th coordinate function of `𝔸(m; Spec k)`, as an element of its function field. -/
def rationalFunctionFieldCoordinate (i : m) : (𝔸(m; Spec (CommRingCat.of k))).functionField :=
  haveI : Nonempty (⊤ : (𝔸(m; Spec (CommRingCat.of k))).Opens) := ⟨⟨genericPoint _, trivial⟩⟩
  (𝔸(m; Spec (CommRingCat.of k))).germToFunctionField ⊤ (AffineSpace.coord _ i)

/-- The base morphism of the `k`-algebra structure is the structure morphism of
`rationalFunctionFieldOver k m`. -/
theorem algebraBaseMap_rationalFunctionField :
    algebraBaseMap k (𝔸(m; Spec (CommRingCat.of k))).functionField =
      (rationalFunctionFieldOver k m).hom :=
  Spec.map_preimage _

end Langlands.GroupScheme
