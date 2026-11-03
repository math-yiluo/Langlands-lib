import Langlands.GroupScheme.Rational.DynamicPositiveSemigroup
import Langlands.GroupScheme.Rational.DynamicSemigroupContainment
import Langlands.GroupScheme.Rational.DynamicFixedSemigroupContainment
import Langlands.GroupScheme.Dynamic.ConnectedProof

/-! # Dynamic functors are the actual cocharacter semigroup subgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.RelativeRoot

/-- The positive comparison needs no ambient connectedness or semigroup
realization premise. -/
theorem dynamicUnipotentSemigroupComparison
    {k : Type u} [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    [Smooth G.X.hom] [IsAffineHom G.X.hom]
    (S : CommGroupScheme (Spec (CommRingCat.of k))) (hS : IsSplitTorus S.toGrp)
    (i : S.toGrp ⟶ G) (ν : cocharacterLattice S) :
    Dynamic.unipotent (CommGroupScheme.groupHom ν ≫ i) =
      semigroupSubgroup (AutomorphicAction.conjugation i) (positiveSemigroup ν) := by
  apply (dynamicUnipotentSemigroupComparison_iff_generators_le G S hS i ν).mpr
  intro F hF
  exact positive_generator_le_dynamicUnipotent G S hS i ν hF

/-- The generator containments and actual Dynamic connectedness give the full
comparison without a semigroup realization or uniqueness premise. -/
theorem dynamicSemigroupComparison_of_connected
    (hConnected : DynamicConnectedStatement.{u}) :
    DynamicSemigroupComparisonStatement.{u} := by
  intro k _ G hSmoothG hAffineG hConnectedG S hS i ν
  let := hSmoothG
  let := hAffineG
  let := hConnectedG
  let χ := CommGroupScheme.groupHom ν ≫ i
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hc := Dynamic.Affine.isRepresentedBy_centralizerHom χ
  have hPClosed : IsSmoothConnectedClosed (Dynamic.parabolic χ) :=
    ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.parabolicHom χ, hp,
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ,
      (dynamicSmooth k G χ _ _).1 hp,
      ((hConnected k G χ _ _).2 inferInstance).1 hp⟩
  have hCClosed : IsSmoothConnectedClosed (Dynamic.centralizer χ) :=
    ⟨Dynamic.Affine.centralizerScheme χ, Dynamic.Affine.centralizerHom χ, hc,
      Dynamic.Affine.isClosedSubgroup_centralizerHom χ,
      (dynamicSmooth k G χ _ _).2.1 hc,
      ((hConnected k G χ _ _).2 inferInstance).2 hc⟩
  have hPLie : HasLieImage (Dynamic.parabolic χ)
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (nonnegativeSemigroup ν)) := by
    intro X
    rw [semigroupWeightSpan_conjugation_nonnegative hS i ν]
    exact (dynamicLie k G χ X.toMul).2.1
  have hCLie : HasLieImage (Dynamic.centralizer χ)
      (semigroupWeightSpan (AutomorphicAction.conjugation i) (zeroSemigroup ν)) := by
    intro X
    rw [semigroupWeightSpan_conjugation_zero hS i ν]
    exact (dynamicLie k G χ X.toMul).1
  refine ⟨le_antisymm ?_ ?_, le_antisymm ?_ ?_,
    dynamicUnipotentSemigroupComparison G S hS i ν⟩
  · exact le_semigroupSubgroup_of_hasLieImage (AutomorphicAction.conjugation i) hS
      (nonnegativeSemigroup ν) hPClosed (Dynamic.parabolic_isStable_conjugation i _) hPLie
  · apply (semigroupSubgroup_le_iff _ _ _).mpr
    intro F hF
    exact nonnegative_generator_le_dynamicParabolic G S hS i ν hF
  · exact le_semigroupSubgroup_of_hasLieImage (AutomorphicAction.conjugation i) hS
      (zeroSemigroup ν) hCClosed (Dynamic.centralizer_isStable_conjugation i _) hCLie
  · apply (semigroupSubgroup_le_iff _ _ _).mpr
    intro F hF
    exact zero_generator_le_dynamicCentralizer G S hS i ν hF

/-- Dynamic functors equal the actual semigroup subgroups for every cocharacter. -/
theorem dynamicSemigroupComparison : DynamicSemigroupComparisonStatement.{u} :=
  dynamicSemigroupComparison_of_connected dynamicConnected

end Langlands.GroupScheme.RelativeRoot
