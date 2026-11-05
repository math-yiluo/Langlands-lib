import Langlands.GroupScheme.AutomorphicAction.SemidirectComplement
import Langlands.GroupScheme.GeometricConnectedness
import Langlands.GroupScheme.Reductive.AlgebraicallyClosedPseudoReductive
import Langlands.GroupScheme.SubgroupRangeTransport

/-! # Reductivity of a semidirect product by a split torus -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.AutomorphicAction

variable {k : Type u} [Field k]
    {S G : GroupScheme (Spec (CommRingCat.of k))}
    (a : AutomorphicAction S G)

/-- An extension of a pseudo-reductive group by an acting split torus is
pseudo-reductive. -/
def SemidirectSplitTorusPseudoReductivityStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (S G : GroupScheme (Spec (CommRingCat.of k)))
    (a : AutomorphicAction S G),
    IsSplitTorus S → IsPseudoReductive G → IsPseudoReductive a.semidirectProduct

/-- A normal smooth connected unipotent subgroup projects trivially to the
split torus, so it is a normal subgroup of the original factor and is trivial. -/
theorem isPseudoReductive_semidirectProduct
    (hS : IsSplitTorus S) (hG : IsPseudoReductive G) :
    IsPseudoReductive a.semidirectProduct := by
  let : IsAffineHom S.X.hom := hS.isAffineHom
  let : Smooth S.X.hom := hS.smooth
  let : ConnectedSpace S.X.left := hS.connectedSpace
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Smooth G.X.hom := hG.smooth
  let : ConnectedSpace G.X.left := hG.connectedSpace
  let : GeometricallyConnected S.X.hom := S.geometricallyConnected_of_connected
  refine ⟨inferInstance, inferInstance, ?_, ?_⟩
  · change ConnectedSpace ↥(pullback G.X.hom S.X.hom)
    infer_instance
  · intro U u hu hUs hUc hU hn
    let : IsClosedImmersion u.hom.hom.left := hu
    let : Mono u.hom.hom := Over.mono_of_mono_left _
    let i := a.semidirectNormalSubgroup u hU hS
    have hi : i ≫ a.semidirectInl = u := a.semidirectNormalSubgroup_comp u hU hS
    have hic : IsClosedSubgroup i :=
      IsClosedSubgroup.of_comp a.isClosedSubgroup_semidirectInl (hi ▸ hu)
    have hin : (SubgroupFunctor.range i).IsNormal :=
      a.semidirectNormalFactor_isNormal u i hi hn
    have hbot := hG.hasTrivialUnipotentRadical U i hic hUs hUc hU hin
    rw [← hi]
    exact (SubgroupFunctor.range_comp_eq_bot_iff i a.semidirectInl).mpr hbot

/-- The all-field pseudo-reductivity assertion. -/
theorem semidirectSplitTorusPseudoReductivity :
    SemidirectSplitTorusPseudoReductivityStatement.{u} := by
  intro k _ S G a hS hG
  exact a.isPseudoReductive_semidirectProduct hS hG

/-- Over an algebraically closed field the semidirect product of a connected
reductive group by a split torus is connected reductive. -/
theorem isConnectedReductive_semidirectProduct_of_isAlgClosed
    [IsAlgClosed k] (hS : IsSplitTorus S) (hG : IsConnectedReductive G) :
    IsConnectedReductive a.semidirectProduct :=
  (a.isPseudoReductive_semidirectProduct hS hG.isPseudoReductive).isConnectedReductive_of_isAlgClosed

end Langlands.GroupScheme.AutomorphicAction
