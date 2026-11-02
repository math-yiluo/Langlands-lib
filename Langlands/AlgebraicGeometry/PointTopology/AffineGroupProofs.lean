import Langlands.AlgebraicGeometry.PointTopology.AffineGroupStatements
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeTopologyExistence
import Langlands.AlgebraicGeometry.PointTopology.AffineSchemeMapProofs
import Langlands.AlgebraicGeometry.PointTopology.AffineProofs
import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Actual affine group-point topology proofs
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory Topology
open _root_.AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.AlgebraicGeometry.PointTopology

variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
variable [TopologicalSpace S]

private theorem tensor_isAffine
    (X Y : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] [IsAffine Y.left] :
    IsAffine (X ⊗ Y).left := by
  have hp : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst X Y) (snd X Y)) (tensorProductIsBinaryProduct X Y)
  exact IsAffine.of_isPullback hp

private theorem tensor_locallyOfFiniteType
    (X Y : Over (Spec (CommRingCat.of R)))
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    LocallyOfFiniteType (X ⊗ Y).hom := by
  have hp : IsPullback (fst X Y).left (snd X Y).left X.hom Y.hom :=
    Over.isPullback_of_binaryFan_isLimit
      (BinaryFan.mk (fst X Y) (snd X Y)) (tensorProductIsBinaryProduct X Y)
  let : LocallyOfFiniteType (snd X Y).left :=
    MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hp inferInstance
  rw [← (snd X Y).w]
  infer_instance

theorem continuous_affineSchemePointPair [IsTopologicalRing S]
    (X Y : Over (Spec (CommRingCat.of R)))
    [IsAffine X.left] [IsAffine Y.left]
    [LocallyOfFiniteType X.hom] [LocallyOfFiniteType Y.hom] :
    letI : IsAffine (X ⊗ Y).left := tensor_isAffine R X Y
    Continuous (X := RingPoint R X S × RingPoint R Y S)
      (Y := RingPoint R (X ⊗ Y) S)
      (fun q => lift q.1 q.2) := by
  let : IsAffine (X ⊗ Y).left := tensor_isAffine R X Y
  let : LocallyOfFiniteType (X ⊗ Y).hom := tensor_locallyOfFiniteType R X Y
  let Z : Over (Spec (CommRingCat.of R)) := Over.mk (𝟙 _)
  let t : IsTerminal Z := Over.mkIdTerminal
  let f : X ⟶ Z := t.from X
  let g : Y ⟶ Z := t.from Y
  have hpb : IsPullback (fst X Y) (snd X Y) f g :=
    IsPullback.of_is_product (tensorProductIsBinaryProduct X Y) t
  let c : PullbackCone f g := PullbackCone.mk (fst X Y) (snd X Y) hpb.w
  let : IsAffine Z.left := inferInstanceAs (IsAffine (Spec (CommRingCat.of R)))
  let : LocallyOfFiniteType Z.hom :=
    inferInstanceAs (LocallyOfFiniteType (𝟙 (Spec (CommRingCat.of R))))
  let : IsAffine c.pt.left := by
    change IsAffine (X ⊗ Y).left
    infer_instance
  let : LocallyOfFiniteType c.pt.hom := by
    change LocallyOfFiniteType (X ⊗ Y).hom
    infer_instance
  have hc := (affineSchemeTopologyExistence_proof R S).2.1 X Y Z f g c hpb.isLimit
  change IsHomeomorph (X := RingPoint R (X ⊗ Y) S)
    (Y := {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g})
    (affineSchemePullbackPointComparison R S c) at hc
  apply hc.isInducing.continuous_iff.mpr
  have hpair : Continuous
      (fun q : RingPoint R X S × RingPoint R Y S =>
        (⟨q, t.hom_ext _ _⟩ :
          {q : RingPoint R X S × RingPoint R Y S // q.1 ≫ f = q.2 ≫ g})) :=
    continuous_id.subtype_mk _
  convert hpair using 1
  funext q
  apply Subtype.ext
  change (lift q.1 q.2 ≫ fst X Y, lift q.1 q.2 ≫ snd X Y) = q
  exact Prod.ext (lift_fst _ _) (lift_snd _ _)

theorem affineGroupTopological_proof [IsTopologicalRing S] :
    AffineGroupTopologicalProperty R S := by
  intro G _ _
  let : Group (RingPoint R G.X S) :=
    inferInstanceAs (Group (ringTest R S ⟶ G.X))
  let : IsAffine (G.X ⊗ G.X).left := tensor_isAffine R G.X G.X
  let : LocallyOfFiniteType (G.X ⊗ G.X).hom :=
    tensor_locallyOfFiniteType R G.X G.X
  refine { continuous_mul := ?_, continuous_inv := ?_ }
  · change Continuous (X := RingPoint R G.X S × RingPoint R G.X S)
      (Y := RingPoint R G.X S) (fun q => lift q.1 q.2 ≫ μ[G.X])
    exact ((affineSchemeTopologyExistence_proof R S).1 _ _ μ[G.X]).comp
      (continuous_affineSchemePointPair R S G.X G.X)
  · change Continuous (X := RingPoint R G.X S) (Y := RingPoint R G.X S)
      (fun p => p ≫ ι[G.X])
    exact (affineSchemeTopologyExistence_proof R S).1 _ _ ι[G.X]

theorem affineGroupFunctorial_proof [IsTopologicalRing S] :
    AffineGroupFunctorialProperty R S := by
  intro G H _ _ _ _
  constructor
  · intro f
    exact continuous_affineSchemePointMap R S f.hom.hom
  · intro e
    let e' : G.X ≅ H.X :=
      (Grp.forget (Over (Spec (CommRingCat.of R)))).mapIso e
    have he : (fun p : RingPoint R G.X S =>
        (p ≫ e.hom.hom.hom : RingPoint R H.X S)) =
        affineSchemePointIsoHomeomorph R S e' := by
      funext p
      exact (affineSchemePointIsoHomeomorph_apply R S e' p).symm
    rw [he]
    exact (affineSchemePointIsoHomeomorph R S e').isHomeomorph

theorem affineGroupClosedImmersion_proof [IsTopologicalRing S] :
    AffineGroupClosedImmersionProperty R S := by
  intro G H _ _ _ _ f _
  refine ⟨isEmbedding_affineSchemePointMap R S f.hom.hom, ?_⟩
  intro _
  exact isClosedEmbedding_affineSchemePointMap R S f.hom.hom

theorem affineGroupLocalCompactness_proof :
    AffineGroupLocalCompactnessProperty R S := by
  constructor
  · intro _ G _
    exact (affineSchemePointHomeomorph R G.X S).isEmbedding.t2Space
  · intro _ _ _ G _ _
    let : LocallyCompactSpace (AlgPoint R (AffineCoordinateRing R G.X) S) :=
      affineLocalCompactness_proof R (AffineCoordinateRing R G.X) S inferInstance
    exact (affineSchemePointHomeomorph R G.X S).isClosedEmbedding.locallyCompactSpace

theorem affineGroupPointProperties_proof :
    AffineGroupPointProperties R S := by
  refine ⟨?_, ?_, ?_, affineGroupLocalCompactness_proof R S⟩
  · intro _
    exact affineGroupTopological_proof R S
  · intro _
    exact affineGroupFunctorial_proof R S
  · intro _
    exact affineGroupClosedImmersion_proof R S

end Langlands.AlgebraicGeometry.PointTopology
