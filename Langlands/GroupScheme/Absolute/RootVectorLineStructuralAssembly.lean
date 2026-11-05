import Langlands.GroupScheme.Rational.TangentVectorLine
import Langlands.GroupScheme.Reductive.RootTangentCurveDimension
import Langlands.GroupScheme.Reductive.RootTangentRankOneReduction
import Langlands.GroupScheme.Rational.SolvableMaximalTorusStructuralAssembly
import Langlands.GroupScheme.Rational.SplitTorusDominationProof
import Langlands.GroupScheme.Absolute.MaximalTorusCentralizerFromQuotient
import Langlands.GroupScheme.ProjectiveTorusFixedPointDimension

/-! # Absolute root vector lines from four structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Four generic structural statements bound the entire intrinsic tangent of
every absolute root subgroup by one. All four inputs remain explicit. -/
theorem absoluteRootTangent_le_one_of_structuralInputs
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hQuot : SolvableTorusQuotientStatement.{u})
    (hDyn : DynamicCentralizerReductiveStatement.{u})
    (k : Type u) [Field k] [IsAlgClosed k]
    (G : GroupScheme (Spec (CommRingCat.of k))) (hG : IsConnectedReductive G) :
    letI := hG.isAffineHom
    ∀ (T : CommGroupScheme (Spec (CommRingCat.of k))) (t : T.toGrp ⟶ G),
      IsSplitSubtorus t → IsMaximalTorus t →
      ∀ α ∈ relativeRoots t,
        Module.finrank k (RelativeRoot.tangentSubmodule
          (RelativeRoot.subgroup t α)) ≤ 1 := by
  have hConj : SolvableMaximalTorusConjugacyStatement.{u} :=
    solvableMaximalTorusConjugacy_of_torusQuotient_and_dominationSplitness
      hQuot unipotentSplitTorusDomination
  have hCent : AlgClosedMaximalTorusCentralizerStatement.{u} :=
    algClosedMaximalTorusCentralizer_fromQuotient hDyn hQuot
  intro T t hsplit hmax α hα
  exact finrank_rootTangent_le_one_of_rankOne hDyn hG hsplit.1 t hmax
    (fun _ hL iL hiL hdep _ hβ =>
      rankOne_rootTangent_le_one_of_projectiveBorelInputs
        hFix hProj hConj hCent hL iL hiL hsplit.1 hdep hβ) hα

/-- The exact absolute root vector-line statement follows from four generic
structural statements. This conditional assembly does not prove them. -/
theorem absoluteRootVectorLine_of_structuralInputs
    (hFix : SolvableProperFixedPointStatement.{u})
    (hProj : ProjectiveTorusFixedPointDimensionStatement.{u})
    (hQuot : SolvableTorusQuotientStatement.{u})
    (hDyn : DynamicCentralizerReductiveStatement.{u}) :
    AbsoluteRootVectorLineStatement.{u} :=
  absoluteRootVectorLine_of_tangentBound
    (absoluteRootTangent_le_one_of_structuralInputs hFix hProj hQuot hDyn)

/-- The three remaining generic structural statements imply the exact absolute
root vector-line statement. -/
def AbsoluteRootVectorLineStructuralReductionStatement : Prop :=
  SolvableProperFixedPointStatement.{u} →
    SolvableTorusQuotientStatement.{u} →
      DynamicCentralizerReductiveStatement.{u} →
        AbsoluteRootVectorLineStatement.{u}

/-- The structural reduction holds, using the published projective fixed-point
bound; its three inputs remain unproved here. -/
theorem absoluteRootVectorLineStructuralReduction :
    AbsoluteRootVectorLineStructuralReductionStatement.{u} :=
  fun hFix hQuot hDyn =>
    absoluteRootVectorLine_of_structuralInputs hFix
      projectiveTorusFixedPointDimension hQuot hDyn

end Langlands.GroupScheme
