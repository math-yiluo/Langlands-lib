import Langlands.GroupScheme.HomScheme.MultiplicativeTypeSubgroupModuli
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth moduli of closed subgroups of multiplicative type -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli

/-- The closed multiplicative-type subgroup functor of a smooth affine group has
a smooth representing scheme with an actual universal family (SGA 3 XI 4.1). -/
def SmoothMultiplicativeTypeSubgroupRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S) [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∃ (M : Over S) (K : GroupScheme M.left)
      (j : K ⟶ (GroupScheme.baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeMultiplicativeType.IsMultiplicativeType K ∧
        Smooth M.hom ∧ IsUniversal j

end Langlands.GroupScheme.MultiplicativeTypeSubgroupModuli
