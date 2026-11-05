import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementReduction
import Langlands.GroupScheme.Reductive.AlmostSimpleNormalSubgroup
import Langlands.GroupScheme.Reductive.NormalCentralizer
import Langlands.GroupScheme.Reductive.CommutingMultiplication
import Langlands.GroupScheme.ImageGenerationReducedProof

/-! # Normal complements from almost-simple generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Choose a commuting normal complement, conditional on the independent
almost-simple generation proposition. The chosen group is the full centralizer,
which need not be smooth. -/
def semisimpleNormalComplementOfAlmostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hG : IsSemisimple G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    CommutingNormalComplement j := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let C := closedNormalCentralizer j hjn
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedSubgroup
  let : IsAffineHom C.group.X.hom := by
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  let : LocallyOfFiniteType C.group.X.hom := by
    rw [← Over.w C.inclusion.hom.hom]
    infer_instance
  have hprod := ImageGeneration.affineFiniteType_tensor H.X C.group.X
  let : IsAffineHom (H ⊗ C.group).X.hom := hprod.1
  let : LocallyOfFiniteType (H ⊗ C.group).X.hom := hprod.2
  let f : H ⊗ C.group ⟶ G :=
    commutingSubgroupMultiplicationHom j C.inclusion C.commute
  have hleft : SubgroupFunctor.range j ≤ SubgroupFunctor.range f :=
    range_left_le_commutingSubgroupMultiplicationHom j C.inclusion C.commute
  have hright : SubgroupFunctor.range C.inclusion ≤ SubgroupFunctor.range f :=
    range_right_le_commutingSubgroupMultiplicationHom j C.inclusion C.commute
  have hf : Flat f.hom.hom.left ∧ Surjective f.hom.hom.left := by
    apply flat_surjective_of_contains_almostSimple_factors hgen hG f
    intro A a hA ha han
    rcases hA.range_le_or_commute_of_normal a j ha hj han hjn with hle | hc
    · exact le_trans hle hleft
    · have hle : SubgroupFunctor.range a ≤ SubgroupFunctor.range C.inclusion := by
        rw [C.range_eq]
        apply (range_le_conjugation_fixedSubgroup_iff j a).mpr
        intro T h x
        exact (hc T x h).symm
      exact le_trans hle hright
  exact ⟨C.group, C.inclusion, C.isClosedSubgroup, C.isNormal, C.commute, hf.1, hf.2⟩

/-- Almost-simple generation suffices for the exact published complement target. -/
theorem semisimpleNormalComplement_of_almostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u}) :
    SemisimpleNormalComplementStatement.{u} := by
  intro k _ _ G H hG j hj hs hc hn
  let : Smooth H.X.hom := hs
  let : ConnectedSpace H.X.left := hc
  exact (semisimpleNormalComplementOfAlmostSimpleGeneration hgen hG j hj hn).exists

end Langlands.GroupScheme
