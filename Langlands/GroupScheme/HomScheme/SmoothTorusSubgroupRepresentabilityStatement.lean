import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Mathlib.AlgebraicGeometry.Morphisms.Smooth

/-! # Smooth moduli of actual closed torus subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- A smooth affine group scheme has a smooth parameter scheme carrying an
actual universal family of closed relative-torus subgroups. -/
def SmoothTorusSubgroupRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom],
    ∃ (M : Over S) (K : GroupScheme M.left)
      (j : K ⟶ (GroupScheme.baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧
        IsUniversal j ∧ Smooth M.hom

end Langlands.GroupScheme.TorusSubgroupModuli
