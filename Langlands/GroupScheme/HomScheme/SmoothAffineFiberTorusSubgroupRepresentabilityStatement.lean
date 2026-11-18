import Langlands.GroupScheme.HomScheme.TorusSubgroupModuli
import Langlands.GroupScheme.RelativeIdentityComponent
import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-! # Smooth torus-subgroup moduli for groups with affine fibres -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.TorusSubgroupModuli

/-- A smooth separated finitely presented group scheme with affine residue
fibres has a smooth parameter scheme carrying an actual universal family of
closed relative-torus subgroups. -/
def SmoothAffineFiberTorusSubgroupRepresentabilityStatement : Prop :=
  ∀ (S : Scheme.{u}) (G : GroupScheme S)
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    (∀ s : S, IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    ∃ (M : Over S) (K : GroupScheme M.left)
      (j : K ⟶ (GroupScheme.baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧
        IsUniversal j ∧ Smooth M.hom

end Langlands.GroupScheme.TorusSubgroupModuli
