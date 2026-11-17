import Langlands.AlgebraicGeometry.Picard.SmoothFamilyQuasiSeparatedRepresentabilityStatement
import Langlands.AlgebraicGeometry.Picard.SmoothFamilyPicardZeroComparisonStatement
import Langlands.AlgebraicGeometry.Picard.DualAbelianScheme
import Langlands.AlgebraicGeometry.Picard.LineBundleDualEvaluation
import Langlands.AlgebraicGeometry.Picard.PicardZeroPullbackProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorProof
import Langlands.AlgebraicGeometry.Modules.PullbackTensorCompatibilityProofs
import Langlands.AlgebraicGeometry.Modules.PullbackTensorUnitProofs
import Langlands.AlgebraicGeometry.Modules.ExplicitPullbackTensorAssociativityProofs
import Langlands.AlgebraicGeometry.Modules.TensorMonoidalComparisonProofs

/-! # Smooth-family universal pairs from universal Picard-zero families -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.AbelianScheme

open Langlands.AlgebraicGeometry.Picard Langlands.Scheme.Modules

variable {S : Scheme.{u}} (A : AbelianScheme S)

/-- Given the smooth-family/translation-invariance comparison, an actual universal
geometric Picard-zero family is universal for smooth-family classes on quasi-separated
tests. -/
theorem isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u}) {P : Over S}
    {L : RigidifiedFamily A P} (hL : IsUniversalPicardZero A L) :
    IsUniversalSmoothFamilyOnQuasiSeparatedTests A L := by
  refine ⟨(comparison.2.2.1 S A P L).mpr hL.1, ?_⟩
  intro T _ q
  exact hL.2 T ⟨q.val, (comparison.2.2.2 S A T q.val).mp q.property⟩

/-- A universal geometric Picard-zero family with abelian-scheme geometry gives an actual
abelian-scheme parameter carrying a smooth-family universal family. The group structure is
the one constructed from Poincaré classification. -/
theorem exists_isUniversalSmoothFamilyOnQuasiSeparatedTests_of_hasDualScheme
    (comparison : SmoothFamilyPicardZeroComparisonStatement.{u})
    (hA : HasDualScheme A) (geometry : DualSchemeGeometry A hA) :
    ∃ (B : AbelianScheme S) (L : RigidifiedFamily A B.X),
      IsUniversalSmoothFamilyOnQuasiSeparatedTests A L := by
  obtain ⟨M, ⟨evaluation⟩⟩ := LineBundle.exists_tensorObj_iso_structureSheaf
    (⟨(poincareFamily A hA).obj.carrier, (poincareFamily A hA).property⟩ :
      LineBundle ((relativeSpace A.X.hom).obj (dualScheme A hA)))
  exact ⟨dualAbelianSchemeFromEvaluation A hA geometry pullbackTensorComparisonIsIso M
      evaluation picardZeroPullback pullbackTensorComposition pullbackTensorUnitCoherence
      explicitPullbackTensorAssociativity tensorMonoidalLeftUnitorComparison
      pullbackTensorSymmetry,
    poincareFamily A hA,
    isUniversalSmoothFamilyOnQuasiSeparatedTests_of_isUniversalPicardZero A comparison
      (poincareFamily_universal A hA)⟩

end Langlands.AbelianScheme
