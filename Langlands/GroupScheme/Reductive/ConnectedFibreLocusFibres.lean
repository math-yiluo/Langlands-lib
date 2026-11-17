import Langlands.GroupScheme.Reductive.ConnectedFibreLocusClosedStatement
import Langlands.GroupScheme.Reductive.IdentityComponentLocusBaseChange
import Langlands.GroupScheme.SmoothConnectedGeometryProof
import Langlands.AlgebraicGeometry.SchemeFiberGeometryLoci
import Langlands.AlgebraicGeometry.GeometricallyConnectedFiberConstructibilityProof

/-! # Connected fibres of smooth affine groups under field extension and base change -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology

set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme

namespace ConnectedFibreLocus

/-- The set of base points with connected residue-field fibre. -/
def connectedFibreLocus {S : Scheme.{u}} (G : GroupScheme S) : Set S :=
  {s | ConnectedSpace (RelativeIdentityComponent.residueFiber G s).X.left}

/-- Connectedness of the underlying scheme transfers along a group-scheme isomorphism. -/
theorem connectedSpace_of_iso {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H)
    [ConnectedSpace G.X.left] : ConnectedSpace H.X.left := by
  have : IsIso e.hom.hom.hom.left :=
    Functor.map_isIso (Grp.forget₂Mon _ ⋙ Mon.forget _ ⋙ Over.forget _) e.hom
  exact e.hom.hom.hom.left.surjective.connectedSpace e.hom.hom.hom.left.continuous

/-- Connectedness of the underlying scheme is invariant under group-scheme isomorphism. -/
theorem connectedSpace_iff_of_iso {S : Scheme.{u}} {G H : GroupScheme S} (e : G ≅ H) :
    ConnectedSpace G.X.left ↔ ConnectedSpace H.X.left :=
  ⟨fun _ => connectedSpace_of_iso e, fun _ => connectedSpace_of_iso e.symm⟩

/-- A smooth affine group over a field is connected exactly when its structure
morphism is geometrically connected. -/
theorem geometricallyConnected_iff_connectedSpace {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    GeometricallyConnected H.X.hom ↔ ConnectedSpace H.X.left := by
  constructor
  · intro h
    exact GeometricallyConnected.connectedSpace_of_subsingleton (f := H.X.hom)
  · intro h
    have hint : GeometricallyIntegral H.X.hom :=
      smoothConnectedAffineGeometry.1 k H inferInstance inferInstance h
    have hirr : GeometricallyIrreducible H.X.hom := inferInstance
    refine ⟨fun K _ y Z fst snd hpb => ?_⟩
    have : IrreducibleSpace Z :=
      hirr.geometrically_irreducibleSpace y fst snd hpb
    infer_instance

/-- Connectedness of a smooth affine group over a field is invariant under every
extension of the field. -/
theorem connectedSpace_baseChange_iff {k K : Type u} [Field k] [Field K] (φ : k →+* K)
    (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    ConnectedSpace ((baseChange (Spec.map (CommRingCat.ofHom φ))).obj H).X.left ↔
      ConnectedSpace H.X.left := by
  constructor
  · intro h
    have : Surjective (Spec.map (CommRingCat.ofHom φ)) :=
      ⟨fun _ => ⟨IsLocalRing.closedPoint _, Subsingleton.elim _ _⟩⟩
    have : Surjective (pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom φ))) :=
      inferInstance
    have : ConnectedSpace ↥(pullback H.X.hom (Spec.map (CommRingCat.ofHom φ))) := h
    exact (pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom φ))).surjective.connectedSpace
      (pullback.fst H.X.hom (Spec.map (CommRingCat.ofHom φ))).continuous
  · intro h
    have hgc : GeometricallyConnected H.X.hom :=
      (geometricallyConnected_iff_connectedSpace H).mpr h
    exact hgc.geometrically_connectedSpace _ _ _ (IsPullback.of_hasPullback _ _)

/-- Group-scheme base change preserves smoothness of the structure morphism. -/
instance smooth_baseChange {S T : Scheme.{u}} (b : T ⟶ S) (H : GroupScheme S)
    [Smooth H.X.hom] : Smooth ((baseChange b).obj H).X.hom :=
  inferInstanceAs (Smooth (pullback.snd H.X.hom b))

/-- Group-scheme base change preserves affineness of the structure morphism. -/
instance isAffineHom_baseChange {S T : Scheme.{u}} (b : T ⟶ S) (H : GroupScheme S)
    [IsAffineHom H.X.hom] : IsAffineHom ((baseChange b).obj H).X.hom :=
  MorphismProperty.pullback_snd H.X.hom b inferInstance

open Langlands.AlgebraicGeometry.SchemeFiberGeometry in
/-- For a smooth affine group, the connected-fibre locus is the geometrically connected
fibre locus of its structure morphism. -/
theorem connectedFibreLocus_eq {S : Scheme.{u}} (G : GroupScheme S) [Smooth G.X.hom]
    [IsAffineHom G.X.hom] :
    connectedFibreLocus G = geometricallyConnectedFiberLocus G.X.hom := by
  ext s
  exact (geometricallyConnected_iff_connectedSpace
    (k := S.residueField s) (RelativeIdentityComponent.residueFiber G s)).symm

open Langlands.AlgebraicGeometry.SchemeFiberGeometry in
/-- The connected-fibre locus of a smooth affine group is locally constructible. -/
theorem isLocallyConstructible_connectedFibreLocus {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    IsLocallyConstructible (connectedFibreLocus G) := by
  rw [connectedFibreLocus_eq]
  exact geometricallyConnectedFiberLocalConstructibility G.X.hom

open Langlands.AlgebraicGeometry.SchemeFiberGeometry in
/-- The connected-fibre locus commutes with arbitrary base change. -/
theorem connectedFibreLocus_baseChange {S T : Scheme.{u}} (b : T ⟶ S) (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] :
    connectedFibreLocus ((baseChange b).obj G) = b ⁻¹' connectedFibreLocus G := by
  rw [connectedFibreLocus_eq, connectedFibreLocus_eq]
  exact geometricallyConnectedFiberLocus_baseChange (IsPullback.of_hasPullback _ _)

open Langlands.AlgebraicGeometry.SchemeFiberGeometry in
/-- A smooth affine group over a field is connected exactly when the unique point of the
base lies in its connected-fibre locus. -/
theorem connectedSpace_iff_mem_connectedFibreLocus {k : Type u} [Field k]
    (H : GroupScheme (Spec (CommRingCat.of k))) [Smooth H.X.hom] [IsAffineHom H.X.hom] :
    ConnectedSpace H.X.left ↔ IsLocalRing.closedPoint k ∈ connectedFibreLocus H := by
  rw [← geometricallyConnected_iff_connectedSpace, connectedFibreLocus_eq,
    ← geometricallyConnectedFiberLocus_eq_univ_iff, Set.eq_univ_iff_forall]
  constructor
  · intro h
    exact h _
  · intro h x
    rwa [Subsingleton.elim x (IsLocalRing.closedPoint k)]

/-- The base change of a smooth affine group along a field-valued point is connected
exactly when the image point lies in the connected-fibre locus. -/
theorem connectedSpace_fieldPoint_iff {S : Scheme.{u}} (G : GroupScheme S)
    [Smooth G.X.hom] [IsAffineHom G.X.hom] {k : Type u} [Field k]
    (b : Spec (CommRingCat.of k) ⟶ S) :
    ConnectedSpace ((baseChange b).obj G).X.left ↔
      b (IsLocalRing.closedPoint k) ∈ connectedFibreLocus G := by
  rw [connectedSpace_iff_mem_connectedFibreLocus, connectedFibreLocus_baseChange]
  rfl

end ConnectedFibreLocus

end Langlands.GroupScheme
