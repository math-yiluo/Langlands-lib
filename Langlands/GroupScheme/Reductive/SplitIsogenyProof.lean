import Langlands.GroupScheme.Reductive.SplitIsogenyChambers
import Langlands.GroupScheme.Reductive.SplitIsogenyDescent
import Langlands.GroupScheme.Reductive.SplitIsogenyGraphFinite
import Langlands.GroupScheme.Reductive.SplitIsogenyAmbientMap
import Langlands.GroupScheme.Reductive.SplitIsogenyReduction
import Langlands.GroupScheme.Reductive.IsogenyRootDatumProof
import Langlands.GroupScheme.Torus.MaximalTransport

/-! # General split reductive isogeny realization and fixed-torus extension -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

open RootDatumIsogenyRealization

/-- Every characteristic-power isogeny of the actual split root data is
realized over the original field, with both prescribed lattice maps. -/
theorem splitIsogenyExistence : SplitIsogenyExistenceStatement.{u} := by
  classical
  intro k _ G G' hG hG' T T' hT hT'
  let := hT.finite_characterLattice
  let := hT.finite_cocharacterLattice
  let := hT'.finite_characterLattice
  let := hT'.finite_cocharacterLattice
  intro i i' hi hi' J J' _ _ P P' _ _ hP hP' f
  let := hG.isAffineHom
  let := hG'.isAffineHom
  let := hG.smooth
  let := hG'.smooth
  let := hG.connectedSpace
  let D := simpleIsogenyGraph i i' hG hG' hT hT' hi hi' hP hP' f
  have ht := torusMap_isIsogeny hT hT' hP.1 hP'.1 f
  let E := D.reductiveGraph hG hG' hT' hi hi' ht hP hP' f
    (fun χ => (torusMap_comp hT' f χ).symm)
  let : IsIso D.envelope.first :=
    D.first_isIsoOfReductive P P' hP hP' hT' f (torusMap_comp hT' f)
      hG hi E.reductive
  have hmax : IsMaximalTorus D.envelope.torusLift :=
    IsMaximalTorus.of_comp (IsClosedSubgroup.of_iso (asIso D.envelope.first))
      (by
        change IsMaximalTorus (D.envelope.torusLift ≫ D.envelope.first)
        rw [D.envelope.torusLift_first]
        exact hi)
  let : IsFinite (CommGroupScheme.groupHom (torusMap hT' f)).hom.hom.left := ht.1
  have hs : IsIsogeny D.envelope.second :=
    D.envelope.second_isIsogeny_of_maximal_torus E.reductive hmax hi'.2.1
      E.projections.secondGeometry.1 E.projections.secondGeometry.2.1
      E.projections.secondGeometry.2.2.2
  obtain ⟨φ, hφ, ht', hsquare, hw, hc⟩ :=
    exists_realization_of_graph_projections hT hT' hP.1 hP'.1 f D.envelope hs
  exact ⟨φ, torusMap hT' f, hφ, ht', hsquare, hw, hc⟩

/-- Both forms of the general split reductive isogeny theorem. -/
theorem splitIsogenyTheorem : SplitIsogenyTheoremStatement.{u} :=
  splitIsogenyTheorem_of_rootDatum_and_existence isogenyRootDatum splitIsogenyExistence

end Langlands.GroupScheme
