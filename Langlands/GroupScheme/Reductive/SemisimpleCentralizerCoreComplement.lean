import Langlands.GroupScheme.Reductive.SemisimpleNormalComplementConstruction
import Langlands.GroupScheme.Reductive.AlmostSimpleGenerationReduction
import Langlands.GroupScheme.Reductive.NormalSemisimpleProof
import Langlands.GroupScheme.Reductive.CommutingMultiplicationFiniteCenters

/-! # Semisimple centralizer-core complements from almost-simple generation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G H : GroupScheme (Spec (CommRingCat.of k))}

/-- Almost-simple generation makes multiplication by the smooth connected
reduced identity component of the full centralizer flat and surjective. -/
theorem flat_surjective_centralizerCoreMultiplication_of_almostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hG : IsSemisimple G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hjn : (SubgroupFunctor.range j).IsNormal)
    (C : ClosedNormalCentralizer j)
    [IsAffineHom C.group.X.hom] [LocallyOfFiniteType C.group.X.hom] :
    Flat (subgroupMultiplication j
      (ReducedSubgroup.identityCoreι C.group ≫ C.inclusion)).left ∧
    Surjective (subgroupMultiplication j
      (ReducedSubgroup.identityCoreι C.group ≫ C.inclusion)).left := by
  let : IsAffineHom G.X.hom := hG.isConnectedReductive.isAffineHom
  let : Smooth G.X.hom := hG.isConnectedReductive.smooth
  let : IsClosedImmersion j.hom.hom.left := hj
  let : IsAffineHom H.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : IsClosedImmersion C.inclusion.hom.hom.left := C.isClosedSubgroup
  let : Mono C.inclusion.hom.hom := Over.mono_of_mono_left _
  let K := ReducedSubgroup.identityCore C.group
  let i : K ⟶ G := ReducedSubgroup.identityCoreι C.group ≫ C.inclusion
  have hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom) := by
    intro T h x
    simpa only [i, Grp.comp_hom_hom, Category.assoc] using
      C.commute T h (x ≫ (ReducedSubgroup.identityCoreι C.group).hom.hom)
  have hprod := ImageGeneration.affineFiniteType_tensor H.X K.X
  let : IsAffineHom (H ⊗ K).X.hom := hprod.1
  let : LocallyOfFiniteType (H ⊗ K).X.hom := hprod.2
  let f : H ⊗ K ⟶ G := commutingSubgroupMultiplicationHom j i hc
  have hleft : SubgroupFunctor.range j ≤ SubgroupFunctor.range f :=
    range_left_le_commutingSubgroupMultiplicationHom j i hc
  have hright : SubgroupFunctor.range i ≤ SubgroupFunctor.range f :=
    range_right_le_commutingSubgroupMultiplicationHom j i hc
  apply flat_surjective_of_contains_almostSimple_factors hgen hG f
  intro A a hA ha han
  rcases hA.range_le_or_commute_of_normal a j ha hj han hjn with hle | hcomm
  · exact le_trans hle hleft
  · let : Smooth A.X.hom := hA.isSemisimple.isConnectedReductive.smooth
    let : ConnectedSpace A.X.left := hA.isSemisimple.isConnectedReductive.connectedSpace
    let : IsClosedImmersion a.hom.hom.left := ha
    let : Mono a.hom.hom := Over.mono_of_mono_left _
    have hle : SubgroupFunctor.range a ≤ SubgroupFunctor.range C.inclusion := by
      rw [C.range_eq]
      apply (range_le_conjugation_fixedSubgroup_iff j a).mpr
      intro T h x
      exact (hcomm T x h).symm
    obtain ⟨b, hb⟩ := SubgroupFunctor.exists_factor_of_range_le hle
    have hcore := range_le_identityCore_of_smooth_connected b
    have hleCore : SubgroupFunctor.range a ≤ SubgroupFunctor.range i := by
      intro T x hx
      obtain ⟨y, hy⟩ := SubgroupFunctor.mem_range.mp hx
      have hby : y ≫ b.hom.hom ∈
          (SubgroupFunctor.range (ReducedSubgroup.identityCoreι C.group)).carrier T :=
        hcore T (SubgroupFunctor.mem_range.mpr ⟨y, rfl⟩)
      obtain ⟨z, hz⟩ := SubgroupFunctor.mem_range.mp hby
      apply SubgroupFunctor.mem_range.mpr
      refine ⟨z, ?_⟩
      change z ≫ (ReducedSubgroup.identityCoreι C.group).hom.hom ≫
        C.inclusion.hom.hom = x
      rw [← Category.assoc, hz, Category.assoc, ← Grp.comp_hom_hom, hb, hy]
    exact le_trans hleCore hright

/-- Choose the reduced centralizer core as a semisimple commuting normal
complement, with the actual multiplication a central isogeny, under the
explicit almost-simple generation hypothesis. -/
def semisimpleCentralizerCoreComplementOfAlmostSimpleGeneration
    (hgen : SemisimpleAlmostSimpleGenerationStatement.{u})
    (hG : IsSemisimple G)
    (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [Smooth H.X.hom] [ConnectedSpace H.X.left]
    (hjn : (SubgroupFunctor.range j).IsNormal) :
    {K : CommutingNormalComplement j //
      IsSemisimple H ∧ IsSemisimple K.group ∧ IsSemisimple (H ⊗ K.group) ∧
      IsCentralIsogeny (commutingSubgroupMultiplicationHom j K.inclusion K.commutes)} := by
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
  let K := ReducedSubgroup.identityCore C.group
  let i : K ⟶ G := ReducedSubgroup.identityCoreι C.group ≫ C.inclusion
  have hi : IsClosedSubgroup i := by
    change IsClosedImmersion
      ((ReducedSubgroup.identityCoreι C.group).hom.hom.left ≫ C.inclusion.hom.hom.left)
    infer_instance
  have hin : (SubgroupFunctor.range i).IsNormal :=
    ReducedSubgroup.isNormal_range_identityCoreι_comp
      C.inclusion C.isClosedSubgroup C.isNormal
  have hc : ∀ (T : Over (Spec (CommRingCat.of k))) (h : T ⟶ H.X) (x : T ⟶ K.X),
      Commute (h ≫ j.hom.hom) (x ≫ i.hom.hom) := by
    intro T h x
    simpa only [i, Grp.comp_hom_hom, Category.assoc] using
      C.commute T h (x ≫ (ReducedSubgroup.identityCoreι C.group).hom.hom)
  have hf := flat_surjective_centralizerCoreMultiplication_of_almostSimpleGeneration
    hgen hG j hj hjn C
  have hH : IsSemisimple H := hG.of_normalSubgroup j hj hjn
  have hK : IsSemisimple K := hG.of_normalSubgroup i hi hin
  let hm := semisimpleCommutingMultiplication j i hj hi hG
    inferInstance inferInstance inferInstance inferInstance hc hf.2
    hH.hasFiniteCenter hK.hasFiniteCenter
  exact ⟨⟨K, i, hi, hin, hc, hf.1, hf.2⟩, hH, hK, hm.property.2, hm.property.1⟩

end Langlands.GroupScheme
