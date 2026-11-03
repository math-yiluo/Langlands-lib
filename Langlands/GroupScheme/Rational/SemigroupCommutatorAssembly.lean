import Langlands.GroupScheme.ImageGenerationSourceTransport
import Langlands.GroupScheme.Rational.AffineCommutatorImageWeightBound
import Langlands.GroupScheme.Rational.SemigroupImageTransport
import Langlands.GroupScheme.Rational.SemigroupCommutatorReduction

/-! # Assembly of the actual commutator generation and weight argument -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates

open PointedCoordinateWeights

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H K : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom] [IsAffineHom K.X.hom]

/-- Apply general pointed generation to the original smooth connected product.
The affine commutator image is not assumed smooth or a group. -/
theorem exists_generated_commutator
    (hGeneration : PointedImageGenerationStatement.{u})
    (hG : Smooth G.X.hom)
    (hH : Smooth H.X.hom) (hHconn : ConnectedSpace H.X.left)
    (hK : Smooth K.X.hom) (hKconn : ConnectedSpace K.X.left)
    (i : H ⟶ G) (j : K ⟶ G) :
    ∃ D : GeneratedImage (imageFactor i j ≫ imageInclusion i j),
      D.HasSmoothConnectedGeneration := by
  obtain ⟨hAff, hFin, _, hInt⟩ := smoothConnectedAffineGeometry.2 k H K
    hH inferInstance hHconn hK inferInstance hKconn
  apply hGeneration k G hG inferInstance (H.X ⊗ K.X) hAff hFin hInt
    (lift (1 : 𝟙_ (Over (Spec (CommRingCat.of k))) ⟶ H.X) 1)
    (imageFactor i j ≫ imageInclusion i j)
  rw [imageFactor_comp, commutatorHom_apply]
  simp only [MonObj.one_comp, inv_one, mul_one]

variable (b : AutomorphicAction S.toGrp G) (c : AutomorphicAction S.toGrp H)
    (d : AutomorphicAction S.toGrp K) (i : H ⟶ G) (j : K ⟶ G)
    (hi : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom))
    (hj : ∀ {T : Over (Spec (CommRingCat.of k))} (s : T ⟶ S.X) (h : T ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom))

include hi hj in
/-- The original commutator source is equivariant for the actual product action. -/
theorem commutator_source_equivariant :
    (c.toPointwiseSchemeAction.prod d.toPointwiseSchemeAction).IsEquivariant
      b.toPointwiseSchemeAction (imageFactor i j ≫ imageInclusion i j) := by
  rw [imageFactor_comp]
  intro T s v
  change (c.toPointwiseSchemeAction.prod d.toPointwiseSchemeAction).act s v ≫
    commutatorHom i j = b.act s (v ≫ commutatorHom i j)
  have hv : v = lift (v ≫ fst H.X K.X) (v ≫ snd H.X K.X) := by simp
  rw [PointwiseSchemeAction.prod_act, AutomorphicAction.toPointwiseSchemeAction_act,
    AutomorphicAction.toPointwiseSchemeAction_act]
  rw [commutatorHom_equivariant b c d i j hi hj]
  rw [← hv]

include hi hj in
/-- The closed envelope of the actual commutator is stable under the ambient
split-torus action. -/
theorem commutator_envelope_stable (hS : IsSplitTorus S.toGrp) :
    b.IsStable (closedImageEnvelope (imageFactor i j ≫ imageInclusion i j)) :=
  b.closedImageEnvelope_isStable hS.isAffineHom
    (c.toPointwiseSchemeAction.prod d.toPointwiseSchemeAction)
    (imageFactor i j ≫ imageInclusion i j)
    (commutator_source_equivariant b c d i j hi hj)

variable (D : GeneratedImage (imageFactor i j ≫ imageInclusion i j))

/-- The generated representative receives a canonical morphism from the actual
affine commutator image by schematic source descent. -/
def generatedImageFactor : imageScheme i j ⟶ D.group.X :=
  letI := imageFactor_schematic i j
  D.sourceFactor (imageFactor i j) (imageInclusion i j)

theorem generatedImageFactor_comp :
    generatedImageFactor i j D ≫ D.inclusion.hom.hom = imageInclusion i j := by
  let := imageFactor_schematic i j
  exact D.sourceFactor_comp (imageFactor i j) (imageInclusion i j)

theorem generatedImageFactor_origin :
    imageOrigin i j ≫ generatedImageFactor i j D = 1 := by
  let := imageFactor_schematic i j
  exact D.sourceFactor_point (imageFactor i j) (imageInclusion i j)
    (imageOrigin i j) (imageOrigin_comp i j)

theorem generatedImageFactor_power_isDominant (n : ℕ)
    (hn : IsDominant (D.powerMap n).left) :
    IsDominant (orderedPowerMap (generatedImageFactor i j D) n).left := by
  let := imageFactor_schematic i j
  exact D.sourceFactor_power_isDominant (imageFactor i j) (imageInclusion i j) n hn

/-- The descended image factor preserves the actual pointed actions. -/
theorem generatedImageFactor_isPointedEquivariant
    (hstable : b.IsStable
      (closedImageEnvelope (imageFactor i j ≫ imageInclusion i j))) :
    IsPointedEquivariant (imageAction b c d i j hi hj)
      (PointedAction.ofGroup (D.action b hstable))
      (generatedImageFactor i j D) := by
  constructor
  · intro T s v
    let : Mono D.inclusion.hom.hom := D.represents.1
    apply (cancel_mono D.inclusion.hom.hom).1
    rw [Category.assoc, generatedImageFactor_comp, PointedAction.ofGroup_act,
      GeneratedImage.action_act_comp, Category.assoc, generatedImageFactor_comp]
    exact imageAction_act_comp b c d i j hi hj s v
  · exact generatedImageFactor_origin i j D

end Langlands.GroupScheme.RelativeRoot.CommutatorCoordinates
