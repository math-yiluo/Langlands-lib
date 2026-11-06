import Langlands.GroupScheme.Absolute.FlagStepReduction
import Langlands.GroupScheme.Absolute.BorelProperQuotientProof
import Langlands.GroupScheme.Absolute.BorelConjugacyProof
import Langlands.GroupScheme.Absolute.FlagInvariantAffineOpenCoverProof
import Langlands.GroupScheme.SchemeActionProperFixedFromKR
import Langlands.GroupScheme.UnipotentAffineOrbitClosedProof

/-! # The flag step of Chevalley's Borel-intersection theorem -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- A smooth connected unipotent closed subgroup contained in every Borel through
an actual maximal torus is contained in every Borel, on every test scheme. -/
theorem unipotentTorusBorelsToAllBorels :
    UnipotentTorusBorelsToAllBorelsStatement.{u} := by
  apply unipotentTorusBorelsToAllBorels_of_geometric_inputs
    someBorelQuotientProper flagInvariantAffineOpenCover borelConjugacy
  intro k _ _ U _ _ _ hU Q hP a hV x
  have : IsProper Q.hom := hP
  exact a.isFixed_of_invariantAffineNeighborhoods_of_kostantRosenlicht
    unipotentAffineOrbitClosed hU hV x

end Langlands.GroupScheme
