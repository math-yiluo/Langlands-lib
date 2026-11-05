import Langlands.AnthropicFLT.P2M.Sol.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral
import Langlands.GroupScheme.RelativeIdentityComponent.OpenConstruction
import Langlands.AlgebraicGeometry.SmoothPointedGeometricConnectedness

/-! # Geometry of the open relative identity restriction -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
  CategoryTheory.CartesianMonoidalCategory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry

/-- A smooth connected scheme over a field is irreducible. -/
theorem irreducibleSpace_of_smooth_connected
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f] [ConnectedSpace X] :
    IrreducibleSpace X := by
  have := P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace f
  infer_instance

end Langlands.AlgebraicGeometry

namespace Langlands.GroupScheme.RelativeIdentityComponent

variable {S : Scheme.{u}} (G : GroupScheme S) (hopen : IsOpen (underlyingSet G))

/-- The actual residue fibre of the open restriction, before supplying a group law. -/
abbrev identityFiberOver (s : S) : Over (Spec (S.residueField s)) :=
  (Over.pullback (S.fromSpecResidueField s)).obj (identityOver G hopen)

/-- The actual inclusion of the raw open restriction on a residue fibre. -/
def identityFiberInclusion (s : S) : identityFiberOver G hopen s ⟶ (residueFiber G s).X :=
  (Over.pullback (S.fromSpecResidueField s)).map (inclusionOver G hopen)

instance (s : S) : IsOpenImmersion (identityFiberInclusion G hopen s).left :=
  MorphismProperty.of_isPullback
    (overPullback_isPullback (S.fromSpecResidueField s) (inclusionOver G hopen)).flip
    inferInstance

/-- Each raw residue-fibre inclusion has image exactly the ambient identity component. -/
theorem range_identityFiberInclusion (s : S) :
    Set.range (identityFiberInclusion G hopen s).left =
      IdentityComponent.identitySet (residueFiber G s) := by
  have hr := range_of_isPullback
    (overPullback_isPullback (S.fromSpecResidueField s) (inclusionOver G hopen))
  change Set.range (identityFiberInclusion G hopen s).left = _ at hr
  rw [hr, range_inclusionOver]
  ext y
  exact fiberι_mem_underlyingSet_iff G s y

instance identityFiberOver_connectedSpace (s : S) :
    ConnectedSpace (identityFiberOver G hopen s).left := by
  have : ConnectedSpace (Set.range (identityFiberInclusion G hopen s).left) :=
    isConnected_iff_connectedSpace.mp (by
      rw [range_identityFiberInclusion]
      exact isConnected_connectedComponent)
  exact (identityFiberInclusion G hopen s).left.isEmbedding.toHomeomorph.connectedSpace_iff.mpr
    inferInstance

/-- The section on the raw residue fibre induced by the ambient unit. -/
def identityFiberOne (s : S) :
    𝟙_ (Over (Spec (S.residueField s))) ⟶ identityFiberOver G hopen s :=
  Functor.LaxMonoidal.ε (Over.pullback (S.fromSpecResidueField s)) ≫
    (Over.pullback (S.fromSpecResidueField s)).map (openOne G hopen)

variable [Smooth G.X.hom]

instance (s : S) : Smooth (identityFiberOver G hopen s).hom := by
  have : Smooth (identityOver G hopen).hom := inferInstance
  change Smooth (pullback.snd (identityOver G hopen).hom (S.fromSpecResidueField s))
  infer_instance

/-- Every residue fibre of the raw open restriction is integral. -/
theorem identityFiberOver_isIntegral (s : S) : IsIntegral (identityFiberOver G hopen s).left :=
  P2MW.S_GoodReductionJacobian_AbelianSchemePropertyBundle_geometricallyIntegral.S17A0.isIntegral_of_smooth_of_connectedSpace (identityFiberOver G hopen s).hom

/-- Every residue fibre of the raw open restriction is irreducible. -/
theorem identityFiberOver_irreducibleSpace (s : S) :
    IrreducibleSpace (identityFiberOver G hopen s).left :=
  Langlands.AlgebraicGeometry.irreducibleSpace_of_smooth_connected
    (identityFiberOver G hopen s).hom

instance identityFiberOver_geometricallyConnected (s : S) :
    GeometricallyConnected (identityFiberOver G hopen s).hom :=
  Langlands.AlgebraicGeometry.geometricallyConnected_of_smooth_connected_section
    (identityFiberOver G hopen s).hom (identityFiberOne G hopen s).left
    (Over.w (identityFiberOne G hopen s))

/-- The raw open restriction has geometrically connected fibres. -/
instance identityOver_geometricallyConnected :
    GeometricallyConnected (identityOver G hopen).hom :=
  (GeometricallyConnected.iff_geometricallyConnected_fiber (identityOver G hopen).hom).mpr fun s =>
    inferInstanceAs (GeometricallyConnected (identityFiberOver G hopen s).hom)

/-- For smooth group schemes only openness remains to establish smooth existence. -/
theorem smoothExistence_of_isOpen
    (h : ∀ (S : Scheme.{u}) (G : GroupScheme S),
      Smooth G.X.hom → IsOpen (underlyingSet G)) : SmoothExistenceStatement.{u} := by
  intro S G hG
  have := hG
  exact exists_of_isOpen G (h S G hG)

end Langlands.GroupScheme.RelativeIdentityComponent
