import Langlands.GroupScheme.Unipotent.CentralAdditiveSubgroupStatement
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.SplitUnipotentStableVectorProof
import Langlands.GroupScheme.Rational.TrivialAction
import Langlands.GroupScheme.Rational.VectorFactorPointedFamilies

/-! # Central additive subgroups of unipotent groups over perfect fields -/

universe u

open CategoryTheory

namespace Langlands.GroupScheme

/-- A nontrivial smooth connected affine unipotent group over a perfect field
of positive characteristic contains a central closed copy of the additive group. -/
theorem perfectFieldCentralAdditiveSubgroup :
    PerfectFieldCentralAdditiveSubgroupStatement.{u} := by
  intro k _ _ _ _ _ U _ _ hConnected hUnipotent hNontrivial
  have hSplit := perfectFieldUnipotentSplit k U hConnected hUnipotent
  obtain ⟨V, z, _, n, coordinates, hz, _, _, _, _, _, hCentral, _, _, hn, _,
      hCoordinates, _⟩ :=
    RelativeRoot.splitUnipotentStableVectorSubgroup k U inferInstance inferInstance
      hConnected hUnipotent hSplit hNontrivial U inferInstance inferInstance
      (AutomorphicAction.trivial U U)
  have hVector : RelativeRoot.IsVectorGroupOfDimension V n := ⟨coordinates, hCoordinates⟩
  obtain ⟨L, j, hj, hLine⟩ := VectorFactorPointedFamilies.exists_closed_vectorLine hVector hn
  let e := hLine.iso.symm
  exact ⟨(e.hom ≫ j) ≫ z, (IsClosedSubgroup.iso_comp e hj).comp hz,
    hCentral.comp (e.hom ≫ j)⟩

end Langlands.GroupScheme
