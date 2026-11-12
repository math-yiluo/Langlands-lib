import Langlands.GroupScheme.SimplyConnected.DerivedCoverStatement
import Langlands.GroupScheme.Derived.RepresentabilityProof
import Langlands.GroupScheme.Derived.SemisimpleProof
import Langlands.GroupScheme.SimplyConnected.CoverExistenceProof

/-! # Proof: existence of simply connected covers of actual reductive derived subgroups -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- **Existence of simply connected derived covers** (CGP, Corollary A.4.11(1), applied to the
derived subgroup). For every connected reductive group `G` over a field, the derived subgroup
`d : D ⟶ G` exists and its source has an actual simply connected central cover `π : C ⟶ D`. -/
theorem simplyConnectedDerivedCoverExistence :
    SimplyConnectedDerivedCoverExistenceStatement.{u} := by
  intro k _ G hG
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨D, d, _, _, hd⟩ := derivedSubgroupRepresentability k G
  obtain ⟨C, π, hπ⟩ := simplyConnectedCoverExistence k D (derivedSubgroupSemisimple k G D d hG hd)
  exact ⟨D, C, d, π, ⟨hG, hd, hπ⟩⟩

end Langlands.GroupScheme
