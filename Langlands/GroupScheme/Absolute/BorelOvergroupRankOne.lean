import Langlands.GroupScheme.Dynamic.CentralizerContainment
import Langlands.GroupScheme.Reductive.RankOneCentralizerDetection
import Langlands.GroupScheme.Reductive.RootReducednessProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Reductive.RootTorusGeneration
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof

/-! # Rank-one centralizers in smooth Borel overgroups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme
namespace AbsoluteBorelOvergroup

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- Occurrence of a root in a subgroup tangent image puts its entire root
line in that image. No smoothness or stability of the subgroup is needed. -/
theorem weightSpace_le_tangentSubmodule_of_mem_support
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {F : SubgroupFunctor G} {α : characterLattice T} (hα : α ∈ roots j)
    (hs : α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j) F) :
    weightSpace j α ≤ RelativeRoot.tangentSubmodule F := by
  obtain ⟨e⟩ := splitRootLieLine k G hG T hT j hj α hα
  have hdim : Module.finrank k (weightSpace j α) = 1 := by
    rw [← e.finrank_eq]
    simp
  obtain ⟨X, hX0, hXα, hXF⟩ := hs
  rw [RelativeRoot.actionWeightSpace_conjugation] at hXα
  rw [eq_span_singleton_of_mem_of_finrank_eq_one hdim hXα hX0]
  exact Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hXF)

variable [Smooth G.X.hom] [ConnectedSpace G.X.left]
    {P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth P.X.hom] [ConnectedSpace P.X.left]

/-- Both root signs in the actual tangent support force containment of the
actual generic rank-one cocharacter centralizer. -/
theorem rankOneCentralizer_le_range_of_both_signs
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (t : T.toGrp ⟶ P) (ht : t ≫ i = j)
    (α : characterLattice T) (hα : α ∈ roots j)
    (hplus : α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i))
    (hminus : -α ∈ RelativeRoot.actionWeightSupport
      (AutomorphicAction.conjugation j) (SubgroupFunctor.range i)) :
    Dynamic.centralizer
      (CommGroupScheme.groupHom (RankOneCentralizerDetection.cocharacter j hT α hα.1) ≫ j) ≤
        SubgroupFunctor.range i := by
  let ζ := RankOneCentralizerDetection.cocharacter j hT α hα.1
  have hTP : SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
    rw [← ht]
    exact SubgroupFunctor.range_comp_le t i
  let : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  have hzero : weightSpace j 0 ≤ RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) :=
    (RelativeRoot.weightSpace_zero_le_tangentSubmodule_range_of_selfCentralizing j
      (maximalTorusCentralizer k G hG T j hj)).trans
        (RelativeRoot.tangentSubmodule_mono hTP)
  have hpos := weightSpace_le_tangentSubmodule_of_mem_support hG hT j hj hα hplus
  have hneg : weightSpace j (-α) ≤ RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) := by
    have hroot : -α ∈ roots j := by
      exact ⟨neg_ne_zero.mpr hα.1, fun hb => by
        obtain ⟨X, hX0, hXα, _⟩ := hminus
        rw [RelativeRoot.actionWeightSpace_conjugation, hb, Submodule.mem_bot] at hXα
        exact hX0 hXα⟩
    exact weightSpace_le_tangentSubmodule_of_mem_support hG hT j hj hroot hminus
  have hregion : RelativeRoot.tangentSubmodule
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ j)) =
        ⨆ β : characterLattice T, ⨆ (_ : latticePairing T β ζ = 0), weightSpace j β := by
    rw [← weightSpace_cocharacter_eq_iSup hT j ζ 0]
    ext X
    exact (dynamicLie k G (CommGroupScheme.groupHom ζ ≫ j) X.toMul).1
  have hLie : RelativeRoot.tangentSubmodule
      (Dynamic.centralizer (CommGroupScheme.groupHom ζ ≫ j)) ≤
        RelativeRoot.tangentSubmodule (SubgroupFunctor.range i) := by
    rw [hregion]
    refine iSup_le fun β => iSup_le fun hβζ => ?_
    by_cases hβ : β = 0
    · simpa only [hβ] using hzero
    by_cases hbot : weightSpace j β = ⊥
    · rw [hbot]
      exact bot_le
    have hdep : ¬ LinearIndependent ℤ ![α, β] :=
      RootReducedness.not_linearIndependent_of_latticePairing_kernelCocharacter
        hT hα.1 (hT.finite_relativeRoots j) ⟨hβ, hbot⟩ hβζ
    rcases rootReducedness k G hG T hT j hj α hα β ⟨hβ, hbot⟩ hdep with heq | heq
    · rw [← heq]
      exact hpos
    · have hβeq : β = -α := by
        simpa only [neg_neg] using (congrArg Neg.neg heq).symm
      rw [hβeq]
      exact hneg
  have hcomp : (CommGroupScheme.groupHom ζ ≫ t) ≫ i =
      CommGroupScheme.groupHom ζ ≫ j := by rw [Category.assoc, ht]
  simpa only [hcomp] using Dynamic.centralizer_le_range_of_tangentSubmodule_le
    i hi (CommGroupScheme.groupHom ζ ≫ t) (by simpa only [hcomp] using hLie)

end AbsoluteBorelOvergroup

/-- Internal rank-one containment interface for the absolute overgroup proof.
The smooth connected overgroup and its torus lift are explicit hypotheses. -/
def AbsoluteBorelOvergroupRankOneContainmentStatement : Prop :=
  ∀ (k : Type u) [Field k]
    (G : GroupScheme (Spec (CommRingCat.of k)))
    [IsAffineHom G.X.hom] [Smooth G.X.hom] [ConnectedSpace G.X.left],
    IsConnectedReductive G →
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k)))
      (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G),
      IsMaximalTorus j →
      ∀ (P : GroupScheme (Spec (CommRingCat.of k)))
        [Smooth P.X.hom] [ConnectedSpace P.X.left]
        (i : P ⟶ G), IsClosedSubgroup i →
        ∀ (t : T.toGrp ⟶ P), t ≫ i = j →
        ∀ (α : characterLattice T) (hα : α ∈ roots j),
          α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
            (SubgroupFunctor.range i) →
          -α ∈ RelativeRoot.actionWeightSupport (AutomorphicAction.conjugation j)
            (SubgroupFunctor.range i) →
          Dynamic.centralizer (CommGroupScheme.groupHom
            (RankOneCentralizerDetection.cocharacter j hT α hα.1) ≫ j) ≤
              SubgroupFunctor.range i

end Langlands.GroupScheme
