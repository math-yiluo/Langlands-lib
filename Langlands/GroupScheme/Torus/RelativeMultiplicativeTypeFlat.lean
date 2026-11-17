import Langlands.GroupScheme.Torus.RelativeMultiplicativeTypeGeometry
import Langlands.AlgebraicGeometry.Morphisms.FppfLocalAtTarget
import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Mathlib.LinearAlgebra.Finsupp.VectorSpace

/-! # Flatness of groups of multiplicative type over a scheme -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace Diagonalizable

/-- Every diagonalizable group is flat over its coefficient ring, including
when its character group has torsion. -/
instance flat (R : CommRingCat.{u}) (Λ : Type u) [AddCommGroup Λ] :
    Flat (groupScheme R Λ).X.hom := by
  change Flat (Spec.map (CommRingCat.ofHom
    (algebraMap R (AddMonoidAlgebra R Λ))))
  apply Flat.SpecMap_iff.mpr
  exact RingHom.flat_algebraMap_iff.mpr inferInstance

end Diagonalizable

end Langlands.GroupScheme
