import Langlands.GroupScheme.Dynamic.AdjointDeterminant
import Langlands.GroupScheme.Reductive.Basic
import Langlands.GroupScheme.Lie.FiniteDimensional

/-! # Structural target for the actual dynamic adjoint determinant -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The structural inputs to the determinant construction follow from connected
reductivity and actual represented dynamic subgroups. -/
def DynamicAdjointDeterminantStructureStatement : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k))),
    IsConnectedReductive G →
    ∀ (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
      (P M U : GroupScheme (Spec (CommRingCat.of k)))
      (iP : P ⟶ G) (iM : M ⟶ G) (iU : U ⟶ G),
      (Dynamic.parabolic χ).IsRepresentedBy iP →
      (Dynamic.centralizer χ).IsRepresentedBy iM →
      (Dynamic.unipotent χ).IsRepresentedBy iU →
      ∃ (_ : IsAffineHom P.X.hom) (_ : IsAffineHom M.X.hom)
        (hUa : IsAffineHom U.X.hom),
        letI := hUa
        IsClosedSubgroup iP ∧ IsClosedSubgroup iM ∧ IsClosedSubgroup iU ∧
        Smooth P.X.hom ∧ Smooth M.X.hom ∧ Smooth U.X.hom ∧
        LocallyOfFiniteType P.X.hom ∧ LocallyOfFiniteType M.X.hom ∧
        LocallyOfFiniteType U.X.hom ∧
        FiniteDimensional k (Additive (lieKernel U k)) ∧
        ∃ d : ℕ, Nonempty (Lie.FiniteCoordinates U d)

end Langlands.GroupScheme
