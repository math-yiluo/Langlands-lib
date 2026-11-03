import Langlands.GroupScheme.Rational.SemigroupCommutatorAssembly
import Langlands.GroupScheme.Rational.SemigroupCoordinateGeneratorTransport
import Langlands.GroupScheme.Rational.PointedPowerSupportTransfer
import Langlands.GroupScheme.Rational.CoordinateSemigroupProof
import Langlands.GroupScheme.ImageGenerationPointed
import Langlands.AlgebraicGeometry.SmoothReducedProof

/-! # The all-test semigroup commutator weight bound -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

open CommutatorCoordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]

/-- The geometric generator bound follows from pointed generation and actual
coordinate/Lie containment, retaining the literal sum of semigroups. -/
theorem semigroupGeneratorCommutatorBound_of_generation_and_containment
    (hGeneration : PointedImageGenerationStatement.{u})
    (hContain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hG : Smooth G.X.hom) (hS : IsSplitTorus S.toGrp)
    (b : AutomorphicAction S.toGrp G) :
    SemigroupGeneratorCommutatorBound b := by
  intro A A' F F' hF hF' T x y hx hy
  obtain ⟨H, i, hi, hic, hH, hHconn⟩ := hF.1
  obtain ⟨K, j, hj, hjc, hK, hKconn⟩ := hF'.1
  let : IsClosedImmersion i.hom.hom.left := hic
  let : IsClosedImmersion j.hom.hom.left := hjc
  let : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  let : IsAffineHom K.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let c := semigroupGeneratorAction b hF i hi
  let d := semigroupGeneratorAction b hF' j hj
  have hci : ∀ {W : Over (Spec (CommRingCat.of k))} (s : W ⟶ S.X) (h : W ⟶ H.X),
      c.act s h ≫ i.hom.hom = b.act s (h ≫ i.hom.hom) :=
    fun s h => b.onRepresentedSubgroup_act_comp i hi hF.2.1 s h
  have hdj : ∀ {W : Over (Spec (CommRingCat.of k))} (s : W ⟶ S.X) (h : W ⟶ K.X),
      d.act s h ≫ j.hom.hom = b.act s (h ≫ j.hom.hom) :=
    fun s h => b.onRepresentedSubgroup_act_comp j hj hF'.2.1 s h
  have hc : CoordinateWeights.support c ⊆ A :=
    coordinate_support_on_generator hContain hS b A F hF i hi hH hHconn
  have hd : CoordinateWeights.support d ⊆ A' :=
    coordinate_support_on_generator hContain hS b A' F' hF' j hj hK hKconn
  obtain ⟨D, hD⟩ := exists_generated_commutator hGeneration hG hH hHconn hK hKconn i j
  have hStable := commutator_envelope_stable b c d i j hci hdj hS
  let : Smooth D.group.X.hom := hD.1
  let : IsAffineHom D.group.X.hom := hD.2.1
  let : GeometricallyConnected D.group.X.hom := hD.2.2.1
  have hDconn : ConnectedSpace D.group.X.left :=
    GeometricallyConnected.connectedSpace_of_subsingleton (f := D.group.X.hom)
  have hImage : PointedCoordinateWeights.support (imageAction b c d i j hci hdj) ⊆
      semigroupSum A A' :=
    image_support_subset_semigroupSum b c d i j hci hdj hS A A' hc hd
  obtain ⟨n, _hn, hDom⟩ := hD.2.2.2
  have hReduced : IsReduced D.group.X.left :=
    Langlands.AlgebraicGeometry.SmoothReducedProof.isReduced_of_smooth_over_field
      k D.group.X.left D.group.X.hom
  have hCoord : CoordinateWeights.support (D.action b hStable) ⊆ semigroupSum A A' :=
    PointedCoordinateWeights.orderedPower_support_subset_semigroup_of_dominant hS
      (imageAction b c d i j hci hdj) (D.action b hStable)
      (generatedImageFactor i j D)
      (generatedImageFactor_isPointedEquivariant b c d i j hci hdj D hStable)
      (semigroupSum A A') hImage n hReduced
      (generatedImageFactor_power_isDominant i j D n hDom)
  have hDgen := generatedImage_isSemigroupGenerator_of_coordinate_support
    hContain hS b D hD.1 hDconn hStable (semigroupSum A A') hCoord
  apply generator_le_semigroupSubgroup b (semigroupSum A A')
    (SubgroupFunctor.range D.inclusion) hDgen T
  have hxrange : x ∈ (SubgroupFunctor.range i).carrier T := by
    rw [hi.2]
    exact hx
  have hyrange : y ∈ (SubgroupFunctor.range j).carrier T := by
    rw [hj.2]
    exact hy
  obtain ⟨x', hx'⟩ := hxrange
  obtain ⟨y', hy'⟩ := hyrange
  change T ⟶ H.X at x'
  change T ⟶ K.X at y'
  change x' ≫ i.hom.hom = x at hx'
  change y' ≫ j.hom.hom = y at hy'
  refine ⟨lift x' y' ≫ D.factor, ?_⟩
  change (lift x' y' ≫ D.factor) ≫ D.inclusion.hom.hom = x * y * x⁻¹ * y⁻¹
  rw [Category.assoc, D.factor_comp, imageFactor_comp, commutatorHom_apply, hx', hy']

/-- Over every field and at every universe, the all-test commutator of the
actual semigroup subgroups has weights in their literal semigroup sum. -/
theorem semigroupCommutator : SemigroupCommutatorStatement.{u} := by
  intro k _ G hG hAff S hS b
  let : IsAffineHom G.X.hom := hAff
  exact semigroupSubgroup_commutator_of_generatorBound b
    (semigroupGeneratorCommutatorBound_of_generation_and_containment
      ImageGeneration.pointedImageGeneration
      CoordinateWeights.coordinateSemigroupComparison.2 hG hS b)

end Langlands.GroupScheme.RelativeRoot
