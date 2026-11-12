import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorPointEquiv
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceWeilRestrictionTensorTopology

/-! # Integral tensor Weil comparison by induced field topologies -/

noncomputable section

universe u

open CategoryTheory Topology
open _root_.AlgebraicGeometry
open scoped TensorProduct

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option backward.isDefEq.respectTransparency false

section InducedFieldTopology

variable (B : Type u) [CommRing B]
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  {A K : Type u} [CommRing A] [Algebra B A]
  [Field K] [Algebra B K] [TopologicalSpace K]

/-- Coefficient change to a field is inducing when the source has the
topology defined through that very coefficient map. -/
theorem isInducing_changeRing_fieldValuedPointTopology (f : A →ₐ[B] K) :
    @IsInducing _ _ (fieldValuedPointTopology B X f)
      (fieldValuedPointTopology B X (AlgHom.id B K)) (RingPoints.changeRing f) := by
  refine @IsInducing.mk _ _ (fieldValuedPointTopology B X f)
    (fieldValuedPointTopology B X (AlgHom.id B K)) (RingPoints.changeRing f) ?_
  rw [fieldValuedPointTopology, fieldValuedPointTopology, induced_compose]
  congr 1
  funext x
  exact CoordinatePointTopologyFacts.fieldValuedPointMap_comp X
    (AlgHom.id B K) f x

end InducedFieldTopology

namespace WeilRestrictionTensorTopology

section Integral

variable (R B C C' : Type u) [CommRing R] [CommRing B] [CommRing C] [Field C']
  [Algebra R B] [Algebra R C] [Algebra R C'] [TopologicalSpace C']
  {ι : Type u} [Finite ι] (D D' : ι → Type u)
  [∀ i, CommRing (D i)] [∀ i, Field (D' i)]
  [∀ i, Algebra C (D i)] [∀ i, Algebra B (D i)]
  [∀ i, Algebra C' (D' i)] [∀ i, Algebra B (D' i)]
  [∀ i, TopologicalSpace (D' i)]
  (e : C ⊗[R] B ≃ₐ[C] (∀ i, D i))
  (he : ∀ (b : B) (i : ι), e (1 ⊗ₜ[R] b) i = algebraMap B (D i) b)
  (e' : C' ⊗[R] B ≃ₐ[C'] (∀ i, D' i))
  (he' : ∀ (b : B) (i : ι), e' (1 ⊗ₜ[R] b) i = algebraMap B (D' i) b)
  (f : C →ₐ[R] C') (g : ∀ i, D i →ₐ[B] D' i)
  (hfg : ∀ (c : C) (i : ι), g i (algebraMap C (D i) c) =
    algebraMap C' (D' i) (f c))
  (X : AlgebraicSpace (Spec (CommRingCat.of B)))
  (h : IsAlgebraicSpace _ ((ringWeilRestriction R B).obj X.toSheaf))
  (hfield : @IsHomeomorph _ _
    (fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C'))
    (coordinateProductTopology B X D' D' (fun i => AlgHom.id B (D' i)))
    (completedTensorSpaceWeilRestrictionPointMap R B C' D' e' he' X h))

/-- A homeomorphism for the field tensor comparison induces the integral
homeomorphism, using the actual compatible coefficient maps and tensor
decompositions on both rows. -/
def integralPointHomeomorph :
    letI : TopologicalSpace (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
      fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) f
    letI : ∀ i, TopologicalSpace (RingPoints B X (D i)) :=
      fun i => fieldValuedPointTopology B X (g i)
    RingPoints R (ringWeilRestrictionSpace R B X h) C ≃ₜ
      (∀ i, RingPoints B X (D i)) := by
  let : TopologicalSpace (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) f
  let : TopologicalSpace (RingPoints R (ringWeilRestrictionSpace R B X h) C') :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) (AlgHom.id R C')
  let (i : ι) : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (g i)
  let (i : ι) : TopologicalSpace (RingPoints B X (D' i)) :=
    fieldValuedPointTopology B X (AlgHom.id B (D' i))
  let E := completedTensorSpaceWeilRestrictionPointsEquiv R B C D e he X h
  let G : (∀ i, RingPoints B X (D i)) → ∀ i, RingPoints B X (D' i) :=
    Pi.map (fun i => RingPoints.changeRing (g i))
  have hlow : IsInducing
      (RingPoints.changeRing (X := ringWeilRestrictionSpace R B X h) f) :=
    isInducing_changeRing_fieldValuedPointTopology R _ f
  have hupp : IsInducing G :=
    IsInducing.piMap (fun i => isInducing_changeRing_fieldValuedPointTopology B X (g i))
  have hcomm : G ∘ E =
      completedTensorSpaceWeilRestrictionPointMap R B C' D' e' he' X h ∘
        RingPoints.changeRing f := by
    funext x i
    change RingPoints.changeRing (g i) (E x i) = _
    rw [completedTensorSpaceWeilRestrictionPointsEquiv_apply]
    exact (completedTensorSpaceWeilRestrictionPointMap_natural
      R B C C' D D' e he e' he' f g hfg X h x i).symm
  exact E.toHomeomorphOfIsInducing
    (hupp.of_comp_iff.mp (hcomm ▸ hfield.isInducing.comp hlow))

@[simp]
theorem integralPointHomeomorph_apply
    (x : RingPoints R (ringWeilRestrictionSpace R B X h) C) (i : ι) :
    integralPointHomeomorph R B C C' D D' e he e' he' f g hfg X h hfield x i =
      completedTensorSpaceWeilRestrictionPointMap R B C D e he X h x i :=
  completedTensorSpaceWeilRestrictionPointsEquiv_apply R B C D e he X h x i

include e' he' hfg hfield in
/-- The original integral tensor factor map is a homeomorphism for the
topologies induced through the specified field coefficient maps. -/
theorem isHomeomorph_completedTensorSpaceWeilRestrictionPointMap_integral :
    @IsHomeomorph _ _
      (fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) f)
      (coordinateProductTopology B X D D' g)
      (completedTensorSpaceWeilRestrictionPointMap R B C D e he X h) := by
  let : TopologicalSpace (RingPoints R (ringWeilRestrictionSpace R B X h) C) :=
    fieldValuedPointTopology R (ringWeilRestrictionSpace R B X h) f
  let (i : ι) : TopologicalSpace (RingPoints B X (D i)) :=
    fieldValuedPointTopology B X (g i)
  have heq :
      (integralPointHomeomorph R B C C' D D' e he e' he' f g hfg X h hfield :
        RingPoints R (ringWeilRestrictionSpace R B X h) C →
          ∀ i, RingPoints B X (D i)) =
        completedTensorSpaceWeilRestrictionPointMap R B C D e he X h :=
    funext fun x => funext fun i =>
      integralPointHomeomorph_apply R B C C' D D' e he e' he' f g hfg X h hfield x i
  rw [← heq]
  exact (integralPointHomeomorph R B C C' D D' e he e' he' f g hfg X h hfield).isHomeomorph

end Integral

end WeilRestrictionTensorTopology

end Langlands.AlgebraicGeometry.AlgebraicSpace
