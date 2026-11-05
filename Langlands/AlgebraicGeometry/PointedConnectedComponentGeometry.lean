import Langlands.AlgebraicGeometry.SmoothPointedGeometricConnectedness
import Langlands.AlgebraicGeometry.LocallyNoetherianConnectedComponentOpenProof
import Langlands.AlgebraicGeometry.SectionComponent
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed

/-! # Geometric connectedness of connected schemes with rational points -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

/-- Over an algebraically closed field, every connected scheme is geometrically connected. -/
theorem geometricallyConnected_of_connected_isAlgClosed
    {k : Type u} [Field k] [IsAlgClosed k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X] :
    GeometricallyConnected f := by
  refine ⟨(geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms
    (P := fun Y : Scheme.{u} => ConnectedSpace Y)).mpr fun K _ _ => ?_⟩
  let t := Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Surjective t :=
    ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have hconn (x : X) : _root_.IsConnected ((pullback.fst f t) ⁻¹' {x}) := by
    have : IrreducibleSpace ((pullback.fst f t).fiber x) :=
      P2MW.S_AlgebraicGeometry_GeometricallyIrreducible_of_irreducibleSpace_of_isAlgClosed.IsAlgClosed.BaseChangeIrreducible.irreducibleSpace_fiber_fst
        f K x
    rw [← Scheme.Hom.range_fiberι, ← Set.image_univ]
    exact isConnected_univ.image _ ((pullback.fst f t).fiberι x).continuous.continuousOn
  apply connectedSpace_iff_univ.mpr
  simpa only [Set.preimage_univ] using
    Topology.IsCoinducing.isConnected_preimage_of_isClosed hconn
      ((pullback.fst f t).isOpenMap.isQuotientMap
        (pullback.fst f t).continuous (pullback.fst f t).surjective).isCoinducing
      isClosed_univ isConnected_univ

/-- A connected scheme over a field with an actual rational section is geometrically
connected. No finite type, smoothness or reducedness assumption is needed. -/
theorem geometricallyConnected_of_connected_section
    {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of k)) [ConnectedSpace X]
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _) :
    GeometricallyConnected f := by
  let K := AlgebraicClosure k
  let t : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of k) :=
    Spec.map (CommRingCat.ofHom (algebraMap k K))
  have : Surjective t := ⟨fun _ => ⟨IsLocalRing.closedPoint K, Subsingleton.elim _ _⟩⟩
  have : IsIntegralHom t :=
    IsIntegralHom.SpecMap_iff.mpr (algebraMap_isIntegral_iff.mpr inferInstance)
  let e' : Spec (CommRingCat.of K) ⟶ pullback f t :=
    pullback.lift (t ≫ e) (𝟙 _)
      (by simp only [Category.assoc, he, Category.comp_id, Category.id_comp])
  let a₀ : ↥(pullback f t) := e' (IsLocalRing.closedPoint K)
  have ha₀ : pullback.fst f t a₀ = e (IsLocalRing.closedPoint k) := by
    change (e' ≫ pullback.fst f t) (IsLocalRing.closedPoint K) = _
    rw [pullback.lift_fst]
    exact congrArg e (Subsingleton.elim _ _)
  have hr : Set.range (pullback.snd e (pullback.fst f t)) =
      pullback.fst f t ⁻¹' {e (IsLocalRing.closedPoint k)} := by
    rw [Scheme.Pullback.range_snd]
    congr 1
    exact Set.range_eq_singleton fun _ => congrArg e (Subsingleton.elim _ _)
  have hsing (a : ↥(pullback f t)) (ha : pullback.fst f t a = pullback.fst f t a₀) :
      a = a₀ := by
    have ha' : a ∈ Set.range (pullback.snd e (pullback.fst f t)) := by
      rw [hr]
      exact ha.trans ha₀
    have ha₀' : a₀ ∈ Set.range (pullback.snd e (pullback.fst f t)) := by
      rw [hr]
      exact ha₀
    obtain ⟨z, rfl⟩ := ha'
    obtain ⟨w, hw⟩ := ha₀'
    have : Subsingleton ↥(pullback e (pullback.fst f t)) :=
      (sectionFiberIso f e he t).hom.homeomorph.toEquiv.subsingleton
    rw [← hw, Subsingleton.elim z w]
  have : ConnectedSpace ↥(pullback f t) :=
    connectedSpace_of_open_closed_singleton_fiber (pullback.fst f t)
      (pullback.fst f t).isOpenMap (pullback.fst f t).isClosedMap a₀ hsing
  have : GeometricallyConnected (pullback.snd f t) :=
    geometricallyConnected_of_connected_isAlgClosed _
  exact geometricallyConnected_of_surjective_baseChange f t

/-- A connected component of a locally Noetherian scheme, as an actual open subscheme. -/
def connectedComponentOpen (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) : X.Opens :=
  ⟨connectedComponent x, locallyNoetherianConnectedComponentOpen_proof X x⟩

instance connectedSpace_connectedComponentOpen
    (X : Scheme.{u}) [IsLocallyNoetherian X] (x : X) :
    ConnectedSpace (connectedComponentOpen X x) :=
  isConnected_iff_connectedSpace.mp isConnected_connectedComponent

/-- The rational section factors through its actual open connected component. -/
def connectedComponentSection {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (e : Spec (CommRingCat.of k) ⟶ X) :
    Spec (CommRingCat.of k) ⟶ connectedComponentOpen X (e (IsLocalRing.closedPoint k)) :=
  IsOpenImmersion.lift (connectedComponentOpen X (e (IsLocalRing.closedPoint k))).ι e (by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨e z, ?_⟩, rfl⟩
    change e z ∈ connectedComponent (e (IsLocalRing.closedPoint k))
    simpa only [Subsingleton.elim z (IsLocalRing.closedPoint k)] using
      (mem_connectedComponent (x := e (IsLocalRing.closedPoint k))))

@[reassoc (attr := simp)]
theorem connectedComponentSection_ι {k : Type u} [Field k] {X : Scheme.{u}}
    [IsLocallyNoetherian X] (e : Spec (CommRingCat.of k) ⟶ X) :
    connectedComponentSection e ≫
      (connectedComponentOpen X (e (IsLocalRing.closedPoint k))).ι = e :=
  IsOpenImmersion.lift_fac ..

/-- The connected component through a rational section point is geometrically connected. -/
theorem geometricallyConnected_connectedComponentOpen
    {k : Type u} [Field k] {X : Scheme.{u}} [IsLocallyNoetherian X]
    (f : X ⟶ Spec (CommRingCat.of k))
    (e : Spec (CommRingCat.of k) ⟶ X) (he : e ≫ f = 𝟙 _) :
    GeometricallyConnected ((connectedComponentOpen X (e (IsLocalRing.closedPoint k))).ι ≫ f) :=
  geometricallyConnected_of_connected_section _ (connectedComponentSection e) (by
    rw [← Category.assoc, connectedComponentSection_ι, he])

namespace SectionComponent

/-- The selected connected component in an actual residue fibre, as an open subscheme. -/
def fiberComponentOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) (y : Y) :
    (f.fiber y).Opens := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField y) inferInstance
  let := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  exact connectedComponentOpen (f.fiber y) (fiberPoint f e he y)

/-- Every selected actual fibre component is geometrically connected over its residue field. -/
theorem geometricallyConnected_fiberComponentOpen {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (e : Y ⟶ X) (he : e ≫ f = 𝟙 Y) (y : Y) :
    GeometricallyConnected
      ((fiberComponentOpen f e he y).ι ≫ f.fiberToSpecResidueField y) := by
  let : LocallyOfFiniteType (f.fiberToSpecResidueField y) :=
    MorphismProperty.pullback_snd f (Y.fromSpecResidueField y) inferInstance
  let := LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField y)
  exact geometricallyConnected_connectedComponentOpen (f.fiberToSpecResidueField y)
    (fiberSection f e he y) (fiberSection_toSpec f e he y)

end SectionComponent

end Langlands.AlgebraicGeometry
