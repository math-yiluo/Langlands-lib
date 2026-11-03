import Langlands.GroupScheme.Rational.TorusActualWeightRepresentative
import Langlands.GroupScheme.Rational.CoordinateSemigroupReduction
import Langlands.GroupScheme.Rational.CoordinateCotangentSupportProof
import Langlands.GroupScheme.Rational.ActionWeightTransport
import Langlands.GroupScheme.Rational.SemigroupClosure
import Langlands.Algebra.GradedIdealSupportProof

/-! # Admissible generators factor through the connected coordinate subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme.TorusActionCoordinates

section Affinization

variable {R : CommRingCat.{u}} {H G : GroupScheme (Spec R)}
    [IsAffineHom H.X.hom] [IsAffineHom G.X.hom]

/-- Affinization commutes with homomorphisms between affine groups. -/
theorem affinizationFactor_comp (f : H ⟶ G) {T : Over (Spec R)} (x : T ⟶ H.X) :
    Lie.affinizationFactor G (x ≫ f.hom.hom) =
      Lie.affinizationFactor H x ≫ f.hom.hom := by
  apply unit_comp_injective G T
  dsimp only
  rw [Lie.unit_affinizationFactor, ← Category.assoc, Lie.unit_affinizationFactor]

end Affinization

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (A : AddSubsemigroup (characterLattice S))

section Represented

variable {H : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    {F : SubgroupFunctor G} (j : H ⟶ G) (hj : F.IsRepresentedBy j)
    (hclosed : IsClosedSubgroup j) (hstable : b.IsStable F)
    (hsupport : RelativeRoot.actionWeightSupport b F ⊆ A)

include hj hclosed hstable hsupport

/-- Every admissible represented generator satisfies the coordinate condition
on every test scheme. -/
theorem range_le_weightHom_of_support :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range (weightHom b e A) := by
  have : IsClosedImmersion j.hom.hom.left := hclosed
  have : IsAffineHom H.X.hom := by
    rw [← j.hom.hom.w]
    infer_instance
  let c := b.onRepresentedSubgroup j hj hstable
  have heq : CoordinateWeights.IsEquivariant c b j.hom.hom :=
    CoordinateWeights.represented_inclusion_equivariant b j hj hstable
  have hLie : RelativeRoot.actionWeightSupport c ⊤ ⊆ A := by
    rw [← RelativeRoot.actionWeightSupport_map j hj.1 c b heq ⊤]
    simpa only [SubgroupFunctor.map_top, hj.2] using hsupport
  have hcoord : CoordinateWeights.support c ⊆ A :=
    ((CoordinateWeights.coordinateSemigroupComparison_of_prerequisites
      Langlands.Algebra.GradedIdealSupport.positiveGeneration
      CoordinateWeights.coordinateWeightDecomposition CoordinateWeights.cotangentLieSupport).2
      k H inferInstance inferInstance inferInstance S
      ⟨I, inferInstance, ⟨e⟩⟩ c A).2 hLie
  intro T x hx
  obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
  apply (mem_range_weightHom_iff b e A _).2
  apply (mem_weightSubgroup_iff_augmentation b e A _).2
  intro χ hχ f hf
  have hpull : CoordinateWeights.augmentationPullback j f = 0 := by
    by_contra hn
    exact hχ (hcoord ⟨CoordinateWeights.augmentationPullback j f, hn,
      CoordinateWeights.augmentationPullback_mem c b j heq χ hf⟩)
  have hz : CoordinateWeights.pullback j.hom.hom f.val = 0 :=
    congrArg Subtype.val hpull
  rw [affinizationFactor_comp j y, CoordinateWeights.coordinates_comp]
  simp only [AlgHom.comp_apply, hz, map_zero]

variable [Smooth G.X.hom]

/-- Every admissible represented generator lies in the connected coordinate subgroup. -/
theorem range_le_connectedWeightHom_of_support :
    SubgroupFunctor.range j ≤ SubgroupFunctor.range (connectedWeightHom b e A) :=
  range_le_connectedWeightHom b e A j
    (range_le_weightHom_of_support b e A j hj hclosed hstable hsupport)

/-- The canonical factor of an admissible represented generator. -/
def generatorWeightFactor : H ⟶ connectedWeightGroupScheme b e A :=
  connectedWeightFactor b e A j
    (range_le_weightHom_of_support b e A j hj hclosed hstable hsupport)

@[reassoc (attr := simp)]
theorem generatorWeightFactor_comp :
    generatorWeightFactor b e A j hj hclosed hstable hsupport ≫
      connectedWeightHom b e A = j :=
  connectedWeightFactor_comp b e A j
    (range_le_weightHom_of_support b e A j hj hclosed hstable hsupport)

end Represented

variable [Smooth G.X.hom]

/-- Every generator in the original definition lies in the connected coordinate subgroup. -/
theorem generator_le_connectedWeightHom {F : SubgroupFunctor G}
    (hF : RelativeRoot.IsSemigroupGenerator b A F) :
    F ≤ SubgroupFunctor.range (connectedWeightHom b e A) := by
  obtain ⟨⟨H, j, hj, hc, hs, hconn⟩, hstable, hsupport⟩ := hF
  let := hs
  let := hconn
  rw [← hj.2]
  exact range_le_connectedWeightHom_of_support b e A j hj hc hstable hsupport

/-- The generated functor is contained in the actual connected coordinate subgroup. -/
theorem semigroupSubgroup_le_connectedWeightHom :
    RelativeRoot.semigroupSubgroup b A ≤
      SubgroupFunctor.range (connectedWeightHom b e A) :=
  (RelativeRoot.semigroupSubgroup_le_iff b A _).2
    (fun _ hF => generator_le_connectedWeightHom b e A hF)

end Langlands.GroupScheme.TorusActionCoordinates
