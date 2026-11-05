import Langlands.GroupScheme.Absolute.RootedProperBorel
import Langlands.GroupScheme.Absolute.PrescribedBorelQuotient
import Langlands.GroupScheme.Dynamic.RootedSolvableQuotientNormalizerProof
import Langlands.GroupScheme.HomogeneousQuotientProjectiveFixedPoints
import Langlands.GroupScheme.Reductive.RankOneCurveCentralizerProof
import Langlands.GroupScheme.Reductive.RankOnePositiveRootBaseChange
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerReduction
import Langlands.GroupScheme.Rational.SolvableMaximalTorusConjugacyProof
import Langlands.GroupScheme.ProjectiveTorusFixedPointDimension
import Langlands.GroupScheme.SolvableProperFixedPointProof

/-! # The rank-one projective Borel route from its remaining structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

section PrescribedBorel

variable {k : Type u} [Field k] [IsAlgClosed k]
    {G B : GroupScheme (Spec (CommRingCat.of k))}
    {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- An actual proper quotient of the prescribed Borel, together with its
projective rank-one dimension bound. -/
def prescribedBorelProjectiveCurveData
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (b : B ⟶ G) (hB : IsBorelSubgroup b)
    (t : T.toGrp ⟶ B) (ht : t ≫ b = i)
    (hconj : MaximalToriAreConjugate B)
    (hc : torusCentralizer i ≤ SubgroupFunctor.range b) :
    {D : IsBorelSubgroup.ProperQuotientData b //
      topologicalKrullDim D.quotient.left ≤ 1} := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  let D := hB.properQuotientData_of_solvableProperFixedPoint hFix
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  have hcp : centralizerPoints i ≤
      (SubgroupFunctor.range b).carrier (Over.mk (𝟙 (Spec (CommRingCat.of k)))) := by
    simpa only [torusCentralizer_carrier_base] using
      hc (Over.mk (𝟙 (Spec (CommRingCat.of k))))
  exact ⟨D, HomogeneousQuotient.dimension_le_one_of_projectiveFixedPointDimension
    b D.projection D.fibers hProj hG i hi hT hdep hB.isClosedSubgroup
    t ht hconj hcp⟩

/-- Construct the proper quotient and a nonidentity normalizer class, obtain
the projective curve bound, and apply regular symmetrization for the original
cocharacter. The subgroup and its actual torus factor are prescribed. -/
theorem positive_roots_eq_of_prescribedBorel_of_projectiveFixedPoints
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hG : IsConnectedReductive G) (i : T.toGrp ⟶ G)
    (hi : IsMaximalTorus i) (hT : IsSplitTorus T.toGrp)
    (hdep : haveI := hG.isAffineHom
      ∀ α ∈ roots i, ∀ β ∈ roots i, ¬ LinearIndependent ℤ ![α, β])
    (b : B ⟶ G) (hB : IsBorelSubgroup b) (hproper : ¬ IsIso b)
    (t : T.toGrp ⟶ B) (ht : t ≫ b = i)
    (hconj : MaximalToriAreConjugate B)
    (hc : torusCentralizer i ≤ SubgroupFunctor.range b)
    (ν : cocharacterLattice T) :
    haveI := hG.isAffineHom
    ∀ {α β : characterLattice T}, α ∈ roots i → β ∈ roots i →
      0 < latticePairing T α ν → 0 < latticePairing T β ν → α = β := by
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  have : ConnectedSpace G.X.left := hG.connectedSpace
  subst i
  let E := prescribedBorelProjectiveCurveData
    hFix hProj hG (t ≫ b) hi hT hdep b hB t rfl hconj hc
  let D := E.val
  have : IsProper D.quotient.hom := D.proper
  have : Smooth D.projection.left := D.smooth
  have : Surjective D.projection.left := D.surjective
  have : QuasiCompact D.projection.left := D.quasiCompact
  have hdim : topologicalKrullDim D.quotient.left ≤ 1 := E.property
  intro α β hα hβ hαν hβν
  let n := nonidentityNormalizerOfRootedSolvableQuotient
    hG.isPseudoReductive (t ≫ b) hi hT hα b hB.isClosedSubgroup
    hB.isSolvableGroupScheme t rfl hconj D.projection D.fibers
  exact HomogeneousQuotient.positive_roots_eq_of_rankOne_curve_torusCentralizer_of_isConnectedReductive
    b D.projection D.fibers hG hB.isClosedSubgroup hB.isSolvableGroupScheme hproper
    hT t hi hdep n.val n.property ν hc hdim hα hβ hαν hβν

end PrescribedBorel

/-- Algebraically closed maximal-torus self-centralization implies the
algebraically closed positive-root uniqueness target. The Borel, its proper
quotient, the projective embedding and the normalizer class are constructed;
solvable proper fixed points, projective fixed-point dimension and solvable
maximal-torus conjugacy are supplied by their published proofs. -/
theorem rankOneAlgClosedPositiveRootUniqueness_of_projectiveBorelInputs
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u}) :
    RankOneAlgClosedPositiveRootUniquenessStatement.{u} := by
  intro k _ _ G hG T hT i hi
  have : IsAffineHom G.X.hom := hG.isAffineHom
  have : Smooth G.X.hom := hG.smooth
  intro hdep ν α hα β hβ hαν hβν
  obtain ⟨B, b, t, hpair, hproper, ht⟩ :=
    exists_proper_isBorelPair_of_relativeRoot hG.isPseudoReductive i hT hi hα
  have : Smooth B.X.hom := hpair.1.smooth
  have : IsAffineHom B.X.hom := hpair.1.isClosedSubgroup.isAffineHom_source
  have : ConnectedSpace B.X.left := hpair.1.connectedSpace
  have hconj : MaximalToriAreConjugate B :=
    solvableMaximalTorusConjugacy k B hpair.1.isSolvableGroupScheme
  have hc : torusCentralizer i ≤ SubgroupFunctor.range b := by
    rw [hCent k G hG T i hi]
    intro Y g hg
    obtain ⟨x, rfl⟩ := SubgroupFunctor.mem_range.mp hg
    refine SubgroupFunctor.mem_range.mpr ⟨x ≫ t.hom.hom, ?_⟩
    rw [Category.assoc, ← Grp.comp_hom_hom, ht]
  exact positive_roots_eq_of_prescribedBorel_of_projectiveFixedPoints
    solvableProperFixedPoint projectiveTorusFixedPointDimension hG i hi hT hdep
    b hpair.1 hproper t ht hconj hc ν hα hβ hαν hβν

/-- The projective Borel route gives the unchanged all-field target from
algebraically closed maximal-torus self-centralization and forward
maximal-torus base change. Solvable proper fixed points, projective fixed-point
dimension and solvable maximal-torus conjugacy are supplied by their published
proofs; two inputs remain explicit. -/
theorem rankOnePositiveRootUniqueness_of_projectiveBorelInputs
    (hCent : AlgClosedMaximalTorusCentralizerStatement.{u})
    (hMax : MaximalTorusBaseChangeForwardStatement.{u}) :
    RankOnePositiveRootUniquenessStatement.{u} :=
  rankOnePositiveRootUniqueness_of_algClosed hMax
    (rankOneAlgClosedPositiveRootUniqueness_of_projectiveBorelInputs hCent)

end Langlands.GroupScheme
