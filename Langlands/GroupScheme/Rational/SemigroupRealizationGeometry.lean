import Langlands.GroupScheme.Rational.TorusWeightGeneratorContainment
import Langlands.GroupScheme.Rational.TorusActualWeightTangent
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness

/-! # Geometric realization of the generated semigroup subgroup -/

noncomputable section

universe u

open CategoryTheory Opposite AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false

namespace Langlands.GroupScheme

namespace TorusActionCoordinates

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom]
    {I : Type u} [Fintype I] [DecidableEq I]
    (b : AutomorphicAction S.toGrp G)
    (e : S.toGrp ≅ splitTorus (Spec (CommRingCat.of k)) I)
    (A : AddSubsemigroup (characterLattice S))

/-- Taking the identity component preserves the exact selected Lie image. -/
theorem hasLieImage_range_connectedWeightHom :
    RelativeRoot.HasLieImage (SubgroupFunctor.range (connectedWeightHom b e A))
      (RelativeRoot.semigroupWeightSpan b A) :=
  (RelativeRoot.hasLieImage_iff_tangentSubmodule_eq _ _).2
    ((tangentSubmodule_range_connectedWeightHom b e A).trans
      (tangentSubmodule_range_weightHom_eq b e A))

/-- The actual connected coordinate subgroup is the original generated functor. -/
theorem range_connectedWeightHom_eq_semigroupSubgroup :
    SubgroupFunctor.range (connectedWeightHom b e A) = RelativeRoot.semigroupSubgroup b A :=
  le_antisymm
    (RelativeRoot.le_semigroupSubgroup_of_hasLieImage b
      ⟨I, inferInstance, ⟨e⟩⟩ A
      (isSmoothConnectedClosed_range_connectedWeightHom b e A)
      (isStable_range_connectedWeightHom b e A)
      (hasLieImage_range_connectedWeightHom b e A))
    (semigroupSubgroup_le_connectedWeightHom b e A)

/-- A representative of the generated all-test functor, constructed from coordinates. -/
def semigroupRepresentative :
    Σ H : GroupScheme (Spec (CommRingCat.of k)),
      {j : H ⟶ G // (RelativeRoot.semigroupSubgroup b A).IsRepresentedBy j} :=
  ⟨connectedWeightGroupScheme b e A, connectedWeightHom b e A,
    ⟨inferInstance, range_connectedWeightHom_eq_semigroupSubgroup b e A⟩⟩

end TorusActionCoordinates

namespace RelativeRoot

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    [Smooth G.X.hom]
    (b : AutomorphicAction S.toGrp G) (hS : IsSplitTorus S.toGrp)
    (A : AddSubsemigroup (characterLattice S))

include hS

/-- The generated semigroup functor has a smooth connected closed realization. -/
theorem isSmoothConnectedClosed_semigroupSubgroup :
    IsSmoothConnectedClosed (semigroupSubgroup b A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let := hI
  let := Fintype.ofFinite I
  classical
  rw [← TorusActionCoordinates.range_connectedWeightHom_eq_semigroupSubgroup b e A]
  exact TorusActionCoordinates.isSmoothConnectedClosed_range_connectedWeightHom b e A

/-- The generated functor has exactly the full selected weight span as Lie image. -/
theorem hasLieImage_semigroupSubgroup :
    HasLieImage (semigroupSubgroup b A) (semigroupWeightSpan b A) := by
  obtain ⟨I, hI, ⟨e⟩⟩ := hS
  let := hI
  let := Fintype.ofFinite I
  classical
  rw [← TorusActionCoordinates.range_connectedWeightHom_eq_semigroupSubgroup b e A]
  exact TorusActionCoordinates.hasLieImage_range_connectedWeightHom b e A

/-- The full maximality equivalence for every smooth connected stable closed subgroup. -/
theorem semigroupSubgroup_maximality (F : SubgroupFunctor G)
    (hF : IsSmoothConnectedClosed F) (hstable : b.IsStable F) :
    actionWeightSupport b F ⊆ A ↔ F ≤ semigroupSubgroup b A :=
  semigroupSubgroup_maximality_of_hasLieImage b hS A
    (hasLieImage_semigroupSubgroup b hS A) F hF hstable

/-- The generated functor is the unique smooth connected stable closed subgroup
with the selected Lie image. -/
theorem eq_semigroupSubgroup_of_exact_lieImage {F : SubgroupFunctor G}
    (hF : IsSmoothConnectedClosed F) (hstable : b.IsStable F)
    (hLie : HasLieImage F (semigroupWeightSpan b A)) :
    F = semigroupSubgroup b A :=
  eq_semigroupSubgroup_of_hasLieImage b hS A
    (isSmoothConnectedClosed_semigroupSubgroup b hS A)
    (hasLieImage_semigroupSubgroup b hS A) hF hstable hLie

end RelativeRoot
end Langlands.GroupScheme
