import Langlands.AlgebraicGeometry.PointTangentSpace
import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
import Mathlib.LinearAlgebra.FiniteDimensional.Defs
import Mathlib.RingTheory.RegularLocalRing.Defs

/-! # Tangent space and local cotangent space at a rational point over a field -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry

namespace Langlands.Scheme

/-- Let `X` be a scheme locally of finite type over a field `k`, with a `k`-rational point given
by a section `e`. Let `R` be the stalk of the structure sheaf at the image point `x` and `T` the
published tangent module `tangentSpaceAtPoint X e`. Then `T` is finite-dimensional over `k`, its
`k`-dimension equals the dimension of the cotangent space `m_R/m_R^2` over the residue field of
`R`, and if `dim_k T ≤ g ≤ dim R` for a natural number `g`, then `R` is a regular local ring.
This proposition is a statement target, not a proof. -/
def FieldPointTangentLocalRegularityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (X : Over (Spec (CommRingCat.of k)))
    (e : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ X),
    LocallyOfFiniteType X.hom →
      let x := e.left (IsLocalRing.closedPoint k)
      let R := X.left.presheaf.stalk x
      let T := Langlands.Scheme.tangentSpaceAtPoint X e
      FiniteDimensional k T ∧
        Module.finrank k T = Module.finrank (IsLocalRing.ResidueField R)
          (IsLocalRing.CotangentSpace R) ∧
        ∀ g : ℕ, Module.finrank k T ≤ g →
          (g : WithBot ℕ∞) ≤ ringKrullDim R → IsRegularLocalRing R

end Langlands.Scheme
