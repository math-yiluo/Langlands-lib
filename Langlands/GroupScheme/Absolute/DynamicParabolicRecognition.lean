import Langlands.GroupScheme.Absolute.RegularRefinement
import Langlands.GroupScheme.Absolute.RegularCocharacterWeights
import Langlands.GroupScheme.Absolute.RegularCocharacterBorelProof
import Langlands.GroupScheme.Absolute.ParabolicTransport
import Langlands.GroupScheme.Dynamic.ParabolicLieCriterion
import Langlands.GroupScheme.Dynamic.SmoothProof
import Langlands.GroupScheme.Dynamic.ConnectedProof
import Langlands.GroupScheme.Dynamic.LieProof
import Langlands.GroupScheme.Lie.SubgroupEqualityProof
import Langlands.GroupScheme.Rational.CocharacterMaximalSplitTorusProof
import Langlands.GroupScheme.Torus.MaximalSplitComparison
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Reductive.AlgebraicExtensionAscent

/-! # Geometric parabolicity of dynamic parabolics -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Containment

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]

/-- Inclusion of nonnegative root supports gives inclusion of the corresponding
nonnegative spans, including the trivial-character weight space. -/
theorem nonnegativeWeightSpan_le_of_root_nonneg (j : T.toGrp ⟶ G)
    (ν ν' : cocharacterLattice T)
    (h : ∀ α ∈ roots j, 0 ≤ latticePairing T α ν → 0 ≤ latticePairing T α ν') :
    nonnegativeWeightSpan j ν ≤ nonnegativeWeightSpan j ν' := by
  refine iSup₂_le fun α hα => ?_
  by_cases h0 : α = 0
  · exact le_iSup₂_of_le α (by simp [h0]) le_rfl
  by_cases hb : weightSpace j α = ⊥
  · rw [hb]
    exact bot_le
  exact le_iSup₂_of_le α (h α ⟨h0, hb⟩ hα) le_rfl

/-- For two cocharacters of the same split torus in a smooth connected affine
group, inclusion of nonnegative root supports implies all-test parabolic inclusion. -/
theorem parabolic_comp_le_of_root_nonneg [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (ν ν' : cocharacterLattice T)
    (h : ∀ α ∈ roots j, 0 ≤ latticePairing T α ν → 0 ≤ latticePairing T α ν') :
    Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν' ≫ j) := by
  refine parabolic_le_parabolic_of_lieKernel dynamicSmooth dynamicConnected lieSubgroupEquality
    _ _ ((SubgroupFunctor.range_comp_le _ j).trans
      ((range_le_centralizer_groupHom_comp j ν).trans (Dynamic.centralizer_le_parabolic _))) ?_
  intro X hX
  apply (dynamicLie k G _ X).2.1.mpr
  have hX' := (dynamicLie k G _ X).2.1.mp hX
  rw [iSup_nat_weightSpace_cocharacter_eq_nonnegativeWeightSpan hT] at hX' ⊢
  exact nonnegativeWeightSpan_le_of_root_nonneg j ν ν' h hX'

/-- The regular refinement defines a dynamic parabolic contained in the original one. -/
theorem parabolic_regularRefinement_le [Smooth G.X.hom] [ConnectedSpace G.X.left]
    (hT : IsSplitTorus T.toGrp) (j : T.toGrp ⟶ G) (ν : cocharacterLattice T) :
    Dynamic.parabolic (CommGroupScheme.groupHom (regularRefinement hT j ν) ≫ j) ≤
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ j) :=
  parabolic_comp_le_of_root_nonneg hT j _ _
    (fun _ hα h => regularRefinement_nonneg hT j ν hα h)

end Containment

/-- An actual Borel subgroup contained, on every test scheme, in a dynamic parabolic. -/
structure DynamicParabolicBorelData {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))}
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) where
  group : GroupScheme (Spec (CommRingCat.of k))
  inclusion : group ⟶ G
  isBorel : IsBorelSubgroup inclusion
  range_le : SubgroupFunctor.range inclusion ≤ Dynamic.parabolic χ

/-- Construct a Borel subgroup inside a dynamic parabolic over an algebraically closed field. -/
def dynamicParabolicBorelData {k : Type u} [Field k] [IsAlgClosed k]
    {G : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) : DynamicParabolicBorelData χ := by
  classical
  apply Classical.choice
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  obtain ⟨T, j, ν, hj, hν⟩ := cocharacterMaximalSplitTorus k G χ
  have hT := hj.1.1
  have hjmax : IsMaximalTorus j := hj.isMaximalTorus
    (fun _ h => h.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting)
  let refinedCochar := regularRefinement hT j ν
  let ψ := CommGroupScheme.groupHom refinedCochar ≫ j
  have : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  refine ⟨⟨Dynamic.Affine.parabolicScheme ψ, Dynamic.Affine.parabolicHom ψ, ?_, ?_⟩⟩
  · exact (regularCocharacterBorel k G hG T j hT hjmax).1 refinedCochar
      (regularRefinement_isRegular hT j ν) _ _
      (Dynamic.Affine.isClosedSubgroup_parabolicHom ψ)
      (Dynamic.Affine.isRepresentedBy_parabolicHom ψ)
  · rw [(Dynamic.Affine.isRepresentedBy_parabolicHom ψ).2]
    exact (parabolic_regularRefinement_le hT j ν).trans (by rw [hν])

/-- Any closed representative of a dynamic parabolic is geometrically parabolic,
over every field and with equality on every test scheme. -/
theorem isParabolicSubgroup_of_range_eq_dynamicParabolic {k : Type u} [Field k]
    {G P : GroupScheme (Spec (CommRingCat.of k))} (hG : IsConnectedReductive G)
    (i : P ⟶ G) (hi : IsClosedSubgroup i)
    (χ : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G)
    (h : SubgroupFunctor.range i = Dynamic.parabolic χ) : IsParabolicSubgroup i := by
  have := hG.isAffineHom
  have := hG.smooth
  have : IsClosedImmersion i.hom.hom.left := hi
  have : Mono i.hom.hom := Over.mono_of_mono_left _
  refine ⟨hi, (dynamicSmooth k G χ P i).1 ⟨inferInstance, h⟩, ?_⟩
  let b := toAlgebraicClosure k
  let F := GroupScheme.baseChange b
  have hGc : IsConnectedReductive (F.obj G) := hG.baseChange_of_algebraicExtension
  let D := dynamicParabolicBorelData hGc (Dynamic.baseChangeCocharacter b χ)
  have hbase : SubgroupFunctor.range (F.map i) =
      Dynamic.parabolic (Dynamic.baseChangeCocharacter b χ) := by
    rw [Dynamic.parabolic_baseChange, ← h, SubgroupFunctor.range_baseChange]
  have : IsClosedImmersion (F.map i).hom.hom.left := hi.baseChange b
  have : Mono (F.map i).hom.hom := Over.mono_of_mono_left _
  have : IsClosedImmersion D.inclusion.hom.hom.left := D.isBorel.isClosedSubgroup
  have : Mono D.inclusion.hom.hom := Over.mono_of_mono_left _
  have hle : SubgroupFunctor.range D.inclusion ≤ SubgroupFunctor.range (F.map i) := by
    rw [hbase]
    exact D.range_le
  exact ⟨D.group, D.inclusion, SubgroupFunctor.factorOfRangeLE hle, D.isBorel,
    SubgroupFunctor.factorOfRangeLE_comp hle⟩

end Langlands.GroupScheme
