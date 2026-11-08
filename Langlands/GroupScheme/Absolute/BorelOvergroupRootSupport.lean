import Langlands.GroupScheme.Absolute.BorelOvergroupRankOne
import Langlands.GroupScheme.Absolute.BorelContainingSubgroupConnected
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerProof
import Langlands.GroupScheme.Reductive.SplitRootLieLineProof
import Langlands.GroupScheme.Lie.TorusCentralizer
import Langlands.GroupScheme.Rational.DynamicSemigroupProof

/-! # Recognizing Borel overgroups from their actual root support -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

namespace AbsoluteBorelOvergroup

open RelativeRoot

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A specified integral cocharacter presents the actual root support of a
subgroup as its nonnegative root halfspace. -/
def HasNonnegativeRootSupport (j : T.toGrp ⟶ G) (F : SubgroupFunctor G)
    (ζ : cocharacterLattice T) : Prop :=
  ∀ α ∈ roots j,
    α ∈ actionWeightSupport (AutomorphicAction.conjugation j) F ↔
      0 ≤ latticePairing T α ζ

omit [IsAffineHom G.X.hom] in
/-- A subgroup containing the acting torus is stable under its conjugation action. -/
theorem isStable_conjugation_of_range_le (j : T.toGrp ⟶ G)
    {F : SubgroupFunctor G} (hT : SubgroupFunctor.range j ≤ F) :
    (AutomorphicAction.conjugation j).IsStable F := by
  intro V t x hx
  rw [AutomorphicAction.conjugation_act]
  have ht := hT V (SubgroupFunctor.mem_range.mpr ⟨t, rfl⟩)
  exact (F.carrier V).mul_mem ((F.carrier V).mul_mem ht hx) ((F.carrier V).inv_mem ht)

/-- The whole zero weight space lies in the tangent of any subgroup containing
a maximal torus, since that torus is its own centralizer. -/
theorem weightSpace_zero_le_tangentSubmodule
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {F : SubgroupFunctor G} (hTF : SubgroupFunctor.range j ≤ F) :
    weightSpace j 0 ≤ tangentSubmodule F := by
  have : IsAffineHom T.toGrp.X.hom := hT.isAffineHom
  intro X hX
  have hXC := Lie.mem_torusCentralizer_of_mem_weightSpace_zero j X.toMul hX
  rw [maximalTorusCentralizer k G hG T j hj] at hXC
  exact hTF _ hXC

/-- Exact agreement of actual root support with a nonnegative cocharacter
halfspace gives the full nonnegative Lie image, including weight zero. -/
theorem tangentSubmodule_eq_nonnegative_of_rootSupport
    [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hTF : SubgroupFunctor.range j ≤ F) (ζ : cocharacterLattice T)
    (hroot : HasNonnegativeRootSupport j F ζ) :
    tangentSubmodule F =
      semigroupWeightSpan (AutomorphicAction.conjugation j) (nonnegativeSemigroup ζ) := by
  have hstable := isStable_conjugation_of_range_le j hTF
  apply le_antisymm
  · apply (hF.actionWeightSupport_subset_iff_tangentSubmodule_le
      (AutomorphicAction.conjugation j) hT hstable (nonnegativeSemigroup ζ)).mp
    intro α hαF
    by_cases hα0 : α = 0
    · subst α
      change 0 ≤ latticePairing T 0 ζ
      simp
    · have hα : α ∈ roots j := by
        obtain ⟨X, hX0, hXα, _⟩ := hαF
        rw [actionWeightSpace_conjugation] at hXα
        refine ⟨hα0, ?_⟩
        intro hbot
        exact hX0 (by simpa only [hbot, Submodule.mem_bot] using hXα)
      exact (hroot α hα).mp hαF
  · refine iSup_le fun α => ?_
    rw [actionWeightSpace_conjugation]
    by_cases hα0 : α.val = 0
    · rw [hα0]
      exact weightSpace_zero_le_tangentSubmodule hG hT j hj hTF
    · by_cases hα : α.val ∈ roots j
      · exact weightSpace_le_tangentSubmodule_of_mem_support hG hT j hj hα
          ((hroot α.val hα).mpr α.property)
      · have hbot : weightSpace j α.val = ⊥ := by
          by_contra hbot
          exact hα ⟨hα0, hbot⟩
        rw [hbot]
        exact bot_le

/-- Once its actual root support is a cocharacter halfspace, a smooth connected
closed subgroup containing the maximal torus is the dynamic parabolic on every test. -/
theorem eq_dynamicParabolic_of_rootSupport
    (hG : IsConnectedReductive G) (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) (hj : IsMaximalTorus j)
    {F : SubgroupFunctor G} (hF : IsSmoothConnectedClosed F)
    (hTF : SubgroupFunctor.range j ≤ F) (ζ : cocharacterLattice T)
    (hroot : HasNonnegativeRootSupport j F ζ) :
    F = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j) := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  let χ := CommGroupScheme.groupHom ζ ≫ j
  have hLie : HasLieImage F
      (semigroupWeightSpan (AutomorphicAction.conjugation j) (nonnegativeSemigroup ζ)) :=
    (hasLieImage_iff_tangentSubmodule_eq _ _).mpr
      (tangentSubmodule_eq_nonnegative_of_rootSupport hG hT j hj hF hTF ζ hroot)
  have hstable := isStable_conjugation_of_range_le j hTF
  have hle : F ≤ Dynamic.parabolic χ :=
    le_dynamicParabolic_of_tangentSubmodule_le G T hT j ζ hF hstable
      (le_of_eq ((hasLieImage_iff_tangentSubmodule_eq _ _).mp hLie))
  have hp := Dynamic.Affine.isRepresentedBy_parabolicHom χ
  have hD : IsSmoothConnectedClosed (Dynamic.parabolic χ) :=
    ⟨Dynamic.Affine.parabolicScheme χ, Dynamic.Affine.parabolicHom χ, hp,
      Dynamic.Affine.isClosedSubgroup_parabolicHom χ,
      (dynamicSmooth k G χ _ _).1 hp,
      ((dynamicConnected k G χ _ _).2 inferInstance).1 hp⟩
  have hDLie : HasLieImage (Dynamic.parabolic χ)
      (semigroupWeightSpan (AutomorphicAction.conjugation j) (nonnegativeSemigroup ζ)) := by
    intro X
    rw [semigroupWeightSpan_conjugation_nonnegative hT j ζ]
    exact (dynamicLie k G χ X.toMul).2.1
  exact hF.eq_of_le_of_hasLieImage hD hle hLie hDLie

end AbsoluteBorelOvergroup

/-- For a smooth closed overgroup of a specified Borel pair, a supplied
nonnegative root-support presentation gives equality with the dynamic parabolic.
Connectedness of the overgroup is derived from the Borel factorization. -/
theorem borelOvergroup_eq_dynamicParabolic_of_rootSupport
    {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (hG : IsConnectedReductive G)
    {T : CommGroupScheme (Spec (CommRingCat.of k))} (hT : IsSplitTorus T.toGrp)
    (j : T.toGrp ⟶ G) {P : GroupScheme (Spec (CommRingCat.of k))}
    [Smooth P.X.hom] (i : P ⟶ G) (hi : IsClosedSubgroup i)
    {B : GroupScheme (Spec (CommRingCat.of k))} (b : B ⟶ P)
    (hpair : IsBorelPair (b ≫ i) j) (ζ : cocharacterLattice T)
    (hroot : AbsoluteBorelOvergroup.HasNonnegativeRootSupport j
      (SubgroupFunctor.range i) ζ) :
    SubgroupFunctor.range i = Dynamic.parabolic (CommGroupScheme.groupHom ζ ≫ j) := by
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  have hP : ConnectedSpace P.X.left :=
    borelContainingSubgroupConnectedStatement k G P B i (b ≫ i) b hi
      inferInstance hpair.1 rfl
  have hF : RelativeRoot.IsSmoothConnectedClosed (SubgroupFunctor.range i) :=
    ⟨P, i, ⟨inferInstance, rfl⟩, hi, inferInstance, hP⟩
  have hTF : SubgroupFunctor.range j ≤ SubgroupFunctor.range i := by
    obtain ⟨f, hf⟩ := hpair.2.2
    have hfi : (f ≫ b) ≫ i = j := (Category.assoc _ _ _).trans hf
    intro V x hx
    obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
    refine SubgroupFunctor.mem_range.mpr ⟨t ≫ (f ≫ b).hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, hfi]
  exact AbsoluteBorelOvergroup.eq_dynamicParabolic_of_rootSupport
    hG hT j hpair.2.1 hF hTF ζ hroot

end Langlands.GroupScheme
