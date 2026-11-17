import Langlands.GroupScheme.Torus.ClosedSubgroupPresentationProof
import Langlands.GroupScheme.Torus.DiagonalizableCharacterProof
import Langlands.GroupScheme.Torus.MultiplicativeTypeGaloisExactnessProof
import Langlands.AbelianScheme.Kernel

/-! # Compatible character presentations of closed diagonalizable subgroups over fields -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.Diagonalizable

variable {k : Type u} [Field k] {M : Type u} [AddCommGroup M]
    {H : GroupScheme (Spec (CommRingCat.of k))}

/-- A diagonalizable presentation of a subgroup, retaining its actual inclusion
as restriction along a surjection of full character groups. -/
structure ClosedSubgroupModel (i : H ⟶ (groupScheme (CommRingCat.of k) M).toGrp) where
  characters : Type u
  [characterGroup : AddCommGroup characters]
  [finiteGeneration : AddGroup.FG characters]
  restriction : M →+ characters
  surjective : Function.Surjective restriction
  iso : H ≅ (groupScheme (CommRingCat.of k) characters).toGrp
  inclusion : iso.hom ≫ restrictMap (CommRingCat.of k) restriction = i

attribute [instance] ClosedSubgroupModel.characterGroup ClosedSubgroupModel.finiteGeneration

/-- Every closed subgroup over a field admits a compatible presentation by a
quotient of the ambient full character group. -/
theorem nonempty_closedSubgroupModel [AddGroup.FG M]
    (i : H ⟶ (groupScheme (CommRingCat.of k) M).toGrp) (hi : IsClosedSubgroup i) :
    Nonempty (ClosedSubgroupModel i) := by
  obtain ⟨N, _, _, ⟨e⟩⟩ := closedSubgroupPresentation k M H i hi
  obtain ⟨p, hp⟩ := (DiagonalizableCharacter.restrictMap_bijective k N M).2 (e.inv ≫ i)
  change restrictMap (CommRingCat.of k) p = e.inv ≫ i at hp
  have hclosed : IsClosedSubgroup (restrictMap (CommRingCat.of k) p) := by
    rw [hp]
    exact IsClosedSubgroup.iso_comp e.symm hi
  exact ⟨{
    characters := N
    restriction := p
    surjective := (MultiplicativeTypeGaloisExactness.isClosedSubgroup_restrictMap_iff k p).1
      hclosed
    iso := e
    inclusion := by rw [hp, Iso.hom_inv_id_assoc] }⟩

/-- Choose the compatible full-character presentation of a closed subgroup. -/
def closedSubgroupModel [AddGroup.FG M]
    (i : H ⟶ (groupScheme (CommRingCat.of k) M).toGrp) (hi : IsClosedSubgroup i) :
    ClosedSubgroupModel i :=
  Classical.choice (nonempty_closedSubgroupModel i hi)

/-- The actual kernel of a map into a separated group has the compatible
closed diagonalizable subgroup presentation, without discarding torsion. -/
def kernelModel [AddGroup.FG M]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsSeparated G.X.hom]
    (f : (groupScheme (CommRingCat.of k) M).toGrp ⟶ G) :
    ClosedSubgroupModel (kernelι f) :=
  closedSubgroupModel (kernelι f) (kernelι_isClosedImmersion f)

end Langlands.GroupScheme.Diagonalizable
