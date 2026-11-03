import Langlands.GroupScheme.Dynamic.ActionStability
import Langlands.GroupScheme.Dynamic.AffineRepresentability
import Langlands.GroupScheme.Dynamic.SmoothConnectedStatement
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.UnipotentConnected
import Langlands.GroupScheme.Dynamic.LieStatement
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Rational.WeightSemigroupStatement
import Langlands.GroupScheme.Rational.CocharacterWeightSums
import Langlands.GroupScheme.Rational.RepresentedLieUniqueness

/-! # The positive Dynamic functor as an admissible semigroup generator -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The positive Dynamic functor is smooth connected closed and stable, with the
exact positive Lie image, without ambient connectedness or semigroup realization. -/
theorem dynamicUnipotent_semigroupData
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    IsSmoothConnectedClosed (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) ∧
    (AutomorphicAction.conjugation i).IsStable
      (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i)) ∧
    HasLieImage (Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i))
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν)) := by
  let χ := CommGroupScheme.groupHom ν ≫ i
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hu := Dynamic.Affine.isRepresentedBy_unipotentHom χ
  have hUClosed : IsSmoothConnectedClosed (Dynamic.unipotent χ) :=
    ⟨Dynamic.Affine.unipotentScheme χ, Dynamic.Affine.unipotentHom χ, hu,
      Dynamic.Affine.isClosedSubgroup_unipotentHom χ,
      (dynamicSmooth k G χ _ _).2.2 hu,
      DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G χ hu⟩
  have hULie : HasLieImage (Dynamic.unipotent χ)
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν)) := by
    intro X
    rw [semigroupWeightSpan_conjugation_positive hS i ν]
    exact (dynamicLie k G χ X.toMul).2.2
  exact ⟨hUClosed, Dynamic.unipotent_isStable_conjugation i _, hULie⟩

/-- The actual positive Dynamic functor is an admissible generator for the
positive pairing region, with no semigroup realization premise. -/
def dynamicUnipotentGenerator
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    {F : SubgroupFunctor G //
      IsSemigroupGenerator (AutomorphicAction.conjugation i) (positiveSemigroup ν) F} :=
  ⟨Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i), by
    obtain ⟨hclosed, hstable, hLie⟩ := dynamicUnipotent_semigroupData G S hS i ν
    exact ⟨hclosed, hstable,
      actionWeightSupport_subset_of_tangentSubmodule_le
        (AutomorphicAction.conjugation i) hS (positiveSemigroup ν) _
        (le_of_eq ((hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie))⟩⟩

@[simp] theorem dynamicUnipotentGenerator_val
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    (dynamicUnipotentGenerator G S hS i ν).val =
      Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := rfl

/-- The positive Dynamic functor lies in the actual generated semigroup subgroup
without a uniqueness or realization premise. -/
theorem dynamicUnipotent_le_semigroupSubgroup
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) ≤
      semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν) := by
  exact generator_le_semigroupSubgroup (AutomorphicAction.conjugation i)
    (positiveSemigroup ν) _ (dynamicUnipotentGenerator G S hS i ν).property

/-- The remaining positive comparison is exactly containment of every admissible
generator in the positive Dynamic functor. -/
theorem dynamicUnipotentSemigroupComparison_iff_generators_le
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
        semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν) ↔
      ∀ F : SubgroupFunctor G,
        IsSemigroupGenerator (AutomorphicAction.conjugation i) (positiveSemigroup ν) F →
        F ≤ Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) := by
  constructor
  · intro h
    exact (semigroupSubgroup_le_iff _ _ _).mp (le_of_eq h.symm)
  · intro h
    exact le_antisymm (dynamicUnipotent_le_semigroupSubgroup G S hS i ν)
      ((semigroupSubgroup_le_iff _ _ _).mpr h)

/-- The positive comparison only needs uniqueness for the specified positive semigroup.
The ambient affine smooth group need not be connected. -/
theorem dynamicUnipotentSemigroupComparison_of_uniqueness
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (hUniq : ∀ F : SubgroupFunctor G, IsSmoothConnectedClosed F →
      (AutomorphicAction.conjugation i).IsStable F →
      HasLieImage F
        (semigroupWeightSpan (AutomorphicAction.conjugation i) (positiveSemigroup ν)) →
      F = semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν)) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν) := by
  obtain ⟨hclosed, hstable, hLie⟩ := dynamicUnipotent_semigroupData G S hS i ν
  exact hUniq _ hclosed hstable hLie

/-- Specialize the positive comparison to the uniqueness clause of the existing
semigroup realization statement, without ambient connectedness. -/
theorem dynamicUnipotentSemigroupComparison_of_semigroupRealization
    (hReal : SemigroupRealizationStatement.{u})
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν) := by
  exact dynamicUnipotentSemigroupComparison_of_uniqueness G S hS i ν
    (hReal k G inferInstance inferInstance S hS
      (AutomorphicAction.conjugation i) (positiveSemigroup ν)).2.2.2.2.2

end Langlands.GroupScheme.RelativeRoot
