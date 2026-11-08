import Langlands.GroupScheme.Absolute.BorelOvergroupCocharacterStatement
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.BorelOvergroupRootInversion
import Langlands.GroupScheme.Absolute.BorelOvergroupRootSupport
import Langlands.GroupScheme.Absolute.BorelOvergroupAveraging

/-! # Actual integral cocharacters of absolute Borel overgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.AbsoluteBorelOvergroup

/-- The given Borel supplies a regular integral cocharacter whose positive
roots all occur in the actual overgroup tangent support. -/
theorem exists_regularCocharacter_positiveRoots_supported
    {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) {P : GroupScheme (Spec (CommRingCat.of k))}
    (i : P ⟶ G) {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ P)
    (hpair : IsBorelPair (b ≫ i) j) :
    ∃ ν : cocharacterLattice T, IsRegularCocharacter j ν ∧
      ∀ α ∈ roots j, 0 < latticePairing T α ν →
        α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i) := by
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨f, hf⟩ := hpair.2.2
  obtain ⟨ν, hν, hνB⟩ :=
    (regularCocharacterBorel k G hG T j hT hpair.2.1).2.2
      B (b ≫ i) f hpair.1 hf
  refine ⟨ν, hν, ?_⟩
  have hle : Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
      SubgroupFunctor.range i := by
    rw [← hνB.2]
    exact SubgroupFunctor.range_comp_le b i
  have hLie : RelativeRoot.HasLieImage
      (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j))
      (RelativeRoot.semigroupWeightSpan (AutomorphicAction.conjugation j)
        (RelativeRoot.nonnegativeSemigroup ν)) := by
    intro X
    rw [RelativeRoot.semigroupWeightSpan_conjugation_nonnegative hT j ν]
    exact (dynamicLie k G (CommGroupScheme.groupHom ν ≫ j) X.toMul).2.1
  intro α hα hpos
  apply RelativeRoot.actionWeightSupport_mono (AutomorphicAction.conjugation j) hle
  apply (RelativeRoot.HasLieImage.mem_actionWeightSupport_iff
    (AutomorphicAction.conjugation j) hT
    (RelativeRoot.nonnegativeSemigroup ν) hLie α).mpr
  exact ⟨le_of_lt hpos, by simpa only [RelativeRoot.actionWeightSpace_conjugation] using hα.2⟩

/-- The original Borel factorization supplies all geometric inputs to the
finite support-stabilizer averaging argument. -/
theorem exists_regularCocharacter_support_and_inverters
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) {P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth P.X.hom] (i : P ⟶ G) (hi : IsClosedSubgroup i)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ P)
    (hpair : IsBorelPair (b ≫ i) j) :
    haveI := hpair.2.1.2.1.mono
    ∃ ν : cocharacterLattice T, IsRegularCocharacter j ν ∧
      (∀ α ∈ roots j, 0 < latticePairing T α ν →
        α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i)) ∧
      ∀ α ∈ roots j,
        α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i) →
        -α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
          (SubgroupFunctor.range i) →
        ∃ w : relativeWeylGroup j,
          relativeWeylCharacterAction j w α = -α ∧
          ∀ β : characterLattice T,
            relativeWeylCharacterAction j w β ∈ RelativeRoot.actionWeightSupport
              (AutomorphicAction.conjugation j) (SubgroupFunctor.range i) ↔
            β ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
              (SubgroupFunctor.range i) := by
  let := hpair.2.1.2.1.mono
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : ConnectedSpace P.X.left :=
    borelContainingSubgroupConnectedStatement k G P B i (b ≫ i) b hi
      inferInstance hpair.1 rfl
  obtain ⟨ν, hν, hpos⟩ :=
    exists_regularCocharacter_positiveRoots_supported hG hT j i b hpair
  obtain ⟨f, hf⟩ := hpair.2.2
  have ht : (f ≫ b) ≫ i = j := (Category.assoc _ _ _).trans hf
  refine ⟨ν, hν, hpos, ?_⟩
  intro α hα hplus hminus
  exact exists_supportPreserving_weylInverter_of_both_signs
    hG hT j hpair.2.1 i hi (f ≫ b) ht α hα hplus hminus

end Langlands.GroupScheme.AbsoluteBorelOvergroup

namespace Langlands.GroupScheme

/-- Every smooth closed overgroup of a specified absolute Borel pair is
presented by an actual integral cocharacter of that pair's torus. -/
theorem absoluteBorelOvergroupCocharacter :
    AbsoluteBorelOvergroupCocharacterStatement.{u} := by
  intro k _ _ G hG T j hT P _ i hi B b hpair
  have : IsAffineHom G.X.hom := hG.isAffineHom
  let := hpair.2.1.2.1.mono
  obtain ⟨ν, hν, hpos, hflip⟩ :=
    AbsoluteBorelOvergroup.exists_regularCocharacter_support_and_inverters
      hG hT j i hi b hpair
  obtain ⟨ζ, hζ⟩ :=
    AbsoluteBorelOvergroup.exists_cocharacter_of_rootSupport_negators
      j hG hT hpair.2.1
      (RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
        (SubgroupFunctor.range i))
      ν hν hpos (by
        intro α hα hplus hminus
        obtain ⟨w, hwα, hw⟩ := hflip α hα hplus hminus
        exact ⟨w, hwα, fun β _ => hw β⟩)
  refine ⟨ζ, ?_⟩
  exact congrArg
    (fun F : SubgroupFunctor G =>
      F.carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))))
    (borelOvergroup_eq_dynamicParabolic_of_rootSupport
      hG hT j i hi b hpair ζ hζ)

end Langlands.GroupScheme
