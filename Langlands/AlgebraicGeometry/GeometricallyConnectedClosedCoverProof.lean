import Langlands.AlgebraicGeometry.GeometricallyConnectedClosedCoverStatement
import Langlands.AlgebraicGeometry.ClosedSubschemeBaseChange

/-! # The geometric connectedness criterion for a finite closed cover -/

noncomputable section

universe u v

open Set TopologicalSpace CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.ComponentIncidence

open GenericImagePattern

/-- The actual base-changed range of a geometrically connected covering piece
 is connected after an arbitrary field extension. -/
theorem isConnected_fieldBaseChangeSubschemeRanges
    {K L : Type u} [Field K] [Field L] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K))
    (e : Spec (CommRingCat.of L) ⟶ Spec (CommRingCat.of K))
    {ι : Type v} {Z : ι → Scheme.{u}} (g : ∀ i, Z i ⟶ X) (i : ι)
    [GeometricallyConnected (g i ≫ f)] :
    _root_.IsConnected (baseChangeSubschemeRanges (pullback.fst f e) g i) := by
  have hconn : ConnectedSpace (pullback (g i ≫ f) e : Scheme.{u}) :=
    pullback_of_geometrically
      (GeometricallyConnected.geometrically_connectedSpace (f := g i ≫ f)) L e
  let : ConnectedSpace (pullback (g i) (pullback.fst f e) : Scheme.{u}) :=
    (pullbackRightPullbackFstIso f e (g i)).hom.homeomorph.connectedSpace_iff.mpr hconn
  exact isConnected_range (pullback.snd (g i) (pullback.fst f e)).continuous

/-- The exact universal closed-cover criterion, with independent index universe. -/
theorem finiteClosedGeometricallyConnectedCoverCriterion :
    FiniteClosedGeometricallyConnectedCoverCriterion.{u, v} := by
  intro K _ X f ι _ Z g _ hcover hpieces
  let : ∀ i, GeometricallyConnected (g i ≫ f) := hpieces
  constructor
  · intro hf
    let := hf
    let : ConnectedSpace X := GeometricallyConnected.connectedSpace_of_subsingleton f
    have hne (i : ι) : (Set.range (g i)).Nonempty := by
      let : ConnectedSpace (Z i) :=
        GeometricallyConnected.connectedSpace_of_subsingleton (g i ≫ f)
      obtain ⟨z⟩ := (inferInstance : Nonempty (Z i))
      exact ⟨g i z, z, rfl⟩
    apply intersectionChainConnected_of_isConnected_iUnion _
      (fun i => (g i).isClosedEmbedding.isClosed_range) hne
    rw [hcover]
    exact isConnected_univ
  · intro hchain
    rw [geometricallyConnected_iff, geometrically_iff_of_isClosedUnderIsomorphisms]
    intro L _ e
    let := surjective_fieldBaseChange f e
    have hcover' := baseChangeSubschemeRanges_cover (pullback.fst f e) g hcover
    have hchain' : IntersectionChainConnected
        (baseChangeSubschemeRanges (pullback.fst f e) g) :=
      (baseChangeSubschemeRanges_chainConnected_iff (pullback.fst f e) g).mpr hchain
    have hclosed (i : ι) :
        IsClosed (baseChangeSubschemeRanges (pullback.fst f e) g i) :=
      (pullback.snd (g i) (pullback.fst f e)).isClosedEmbedding.isClosed_range
    have hconn (i : ι) :
        _root_.IsConnected (baseChangeSubschemeRanges (pullback.fst f e) g i) :=
      isConnected_fieldBaseChangeSubschemeRanges f e g i
    apply connectedSpace_iff_univ.mpr
    rw [← hcover']
    exact (isConnected_iUnion_iff_intersectionChainConnected _ hclosed hconn).mpr hchain'

end Langlands.AlgebraicGeometry.ComponentIncidence
