import Langlands.GroupScheme.Reductive.NormalIsogenyComplementReduction
import Langlands.GroupScheme.Derived.AlmostSimplePerfect

/-! # Normal-isogeny complements from almost-simple generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- Almost-simple generation alone implies the exact arbitrary-field
normal-isogeny-complement proposition. -/
theorem semisimpleNormalIsogenyComplement_of_generation
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u}) :
    SemisimpleNormalIsogenyComplementStatement.{u} :=
  semisimpleNormalIsogenyComplement_of_generation_and_perfectness hgen
    (algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration hgen)

/-- Choose the actual semisimple commuting normal complement over the
original field, with almost-simple generation as the sole structural input. -/
def semisimpleNormalIsogenyComplementOfGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    {k : Type u} [Field k] {G H : GroupScheme (Spec (CommRingCat.of k))}
    (hG : IsSemisimple G) (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    {K : CommutingNormalComplement j //
      IsSemisimple H ∧ IsSemisimple K.group ∧ IsSemisimple (H ⊗ K.group) ∧
      IsCentralIsogeny (commutingSubgroupMultiplicationHom j K.inclusion K.commutes)} :=
  semisimpleNormalIsogenyComplementOfGenerationAndPerfectness hgen
    (algebraicallyClosedSemisimplePerfect_of_almostSimpleGeneration hgen) hG j hj hjn

end Langlands.GroupScheme
