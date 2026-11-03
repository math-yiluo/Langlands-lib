import Langlands.GroupScheme.Rational.SemigroupImageTransport

/-! # Coordinate and intrinsic Lie bounds for generated commutators -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G H : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom] [IsAffineHom H.X.hom]

/-- The actual restricted action on a supplied representative of a semigroup
generator. -/
def semigroupGeneratorAction (b : AutomorphicAction S.toGrp G)
    {A : AddSubsemigroup (characterLattice S)} {F : SubgroupFunctor G}
    (hF : IsSemigroupGenerator b A F) (i : H ⟶ G) (hi : F.IsRepresentedBy i) :
    AutomorphicAction S.toGrp H :=
  b.onRepresentedSubgroup i hi hF.2.1

/-- The actual action on an admissible representative satisfies its input
coordinate-support bound, conditional on coordinate/Lie containment. -/
theorem coordinate_support_on_generator
    (hcontain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    (A : AddSubsemigroup (characterLattice S)) (F : SubgroupFunctor G)
    (hF : IsSemigroupGenerator b A F) (i : H ⟶ G)
    (hi : F.IsRepresentedBy i) (hH : Smooth H.X.hom)
    (hHconn : ConnectedSpace H.X.left) :
    CoordinateWeights.support (semigroupGeneratorAction b hF i hi) ⊆ A := by
  let c := semigroupGeneratorAction b hF i hi
  apply (hcontain k H hH inferInstance hHconn S hS c A).mpr
  have he := actionWeightSupport_map i hi.1 c b
    (fun _ s x => b.onRepresentedSubgroup_act_comp i hi hF.2.1 s x) ⊤
  rw [SubgroupFunctor.map_top, hi.2] at he
  rw [← he]
  exact hF.2.2

/-- Coordinate support of a smooth connected generated representative makes
its actual closed range an admissible generator. -/
theorem generatedImage_isSemigroupGenerator_of_coordinate_support
    (hcontain : CoordinateWeights.AugmentationLieContainmentStatement.{u})
    (hS : IsSplitTorus S.toGrp) (b : AutomorphicAction S.toGrp G)
    {V : Over (Spec (CommRingCat.of k))} {f : V ⟶ G.X}
    (D : GeneratedImage f) [IsAffineHom D.group.X.hom]
    (hDsm : Smooth D.group.X.hom) (hDconn : ConnectedSpace D.group.X.left)
    (hstable : b.IsStable (closedImageEnvelope f))
    (A : AddSubsemigroup (characterLattice S))
    (hA : CoordinateWeights.support (D.action b hstable) ⊆ A) :
    IsSemigroupGenerator b A (SubgroupFunctor.range D.inclusion) := by
  refine ⟨⟨D.group, D.inclusion, ⟨D.represents.1, rfl⟩,
    D.closed, hDsm, hDconn⟩, ?_, ?_⟩
  · rw [D.represents.2]
    exact hstable
  · have he := actionWeightSupport_map D.inclusion D.represents.1
      (D.action b hstable) b (fun _ s x => D.action_act_comp b hstable s x) ⊤
    rw [SubgroupFunctor.map_top] at he
    rw [he]
    exact (hcontain k D.group hDsm inferInstance hDconn S hS
      (D.action b hstable) A).mp hA

end Langlands.GroupScheme.RelativeRoot
