import Langlands.GroupScheme.Multiplicative
import Langlands.AlgebraicGeometry.PointedConnectedComponentGeometry

/-! # Connected residue fibres of group schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}}

/-- Connectedness of the actual canonical residue-field fibres of a group scheme. -/
def HasConnectedResidueFibres (G : GroupScheme S) : Prop :=
  ∀ s : S, ConnectedSpace
    ((GroupScheme.baseChange (S.fromSpecResidueField s)).obj G).X.left

/-- The unit makes each connected residue fibre geometrically connected, without
finiteness or smoothness hypotheses on the group scheme. -/
theorem geometricallyConnected_of_connectedResidueFibres (G : GroupScheme S)
    (hG : HasConnectedResidueFibres G) : GeometricallyConnected G.X.hom := by
  apply (GeometricallyConnected.iff_geometricallyConnected_fiber G.X.hom).mpr
  intro s
  let Gs := (GroupScheme.baseChange (S.fromSpecResidueField s)).obj G
  have : ConnectedSpace Gs.X.left := hG s
  change GeometricallyConnected Gs.X.hom
  exact Langlands.AlgebraicGeometry.geometricallyConnected_of_connected_section Gs.X.hom
    (1 : 𝟙_ (Over (Spec (S.residueField s))) ⟶ Gs.X).left (Over.w _)

/-- For group schemes, connected canonical residue fibres are equivalent to
geometric connectedness of the structure morphism. -/
theorem hasConnectedResidueFibres_iff_geometricallyConnected (G : GroupScheme S) :
    HasConnectedResidueFibres G ↔ GeometricallyConnected G.X.hom := by
  constructor
  · exact geometricallyConnected_of_connectedResidueFibres G
  · intro h
    let := h
    intro s
    change ConnectedSpace (G.X.hom.fiber s)
    infer_instance

/-- Connected residue fibres remain connected after arbitrary base change. -/
theorem HasConnectedResidueFibres.baseChange {G : GroupScheme S}
    (hG : HasConnectedResidueFibres G) (b : S' ⟶ S) :
    HasConnectedResidueFibres ((GroupScheme.baseChange b).obj G) := by
  apply (hasConnectedResidueFibres_iff_geometricallyConnected _).mpr
  let := geometricallyConnected_of_connectedResidueFibres G hG
  change GeometricallyConnected (pullback.snd G.X.hom b)
  infer_instance

/-- In particular, every field-valued fibre is connected. -/
theorem connectedSpace_fieldFiber_of_connectedResidueFibres (G : GroupScheme S)
    (hG : HasConnectedResidueFibres G) {k : Type u} [Field k]
    (x : Spec (CommRingCat.of k) ⟶ S) :
    ConnectedSpace ↥(pullback G.X.hom x) := by
  let := geometricallyConnected_of_connectedResidueFibres G hG
  exact (geometrically_iff_of_isClosedUnderIsomorphisms.mp
    (GeometricallyConnected.geometrically_connectedSpace (f := G.X.hom))) k x

end Langlands.GroupScheme
