import Langlands.Representation.Aubert.General.RationalCompactTranslateCoefficientBoundStatement
import Langlands.Representation.Aubert.General.RationalLatticeCoefficientDecayProof
import Langlands.Representation.MatrixCoefficient.CompactTranslateLatticeBoundProof
import Langlands.Representation.Smooth.FixedVectors.OrderProof

/-! # Compact translates of the actual rational coefficient bound -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal BigOperators

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme BruhatTits.SpecialCompact
open Langlands.AlgebraicGeometry.PointTopology

/-- Choose a common small fixing subgroup for each smooth input pair and then
apply the generic finite compact-orbit argument. -/
theorem rationalCompactTranslateCoefficientBound :
    RationalCompactTranslateCoefficientBoundStatement.{u, v, w} := by
  intro k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ ν hν hStandard hU A hA hstrict K0 hBasis
  classical
  obtain ⟨B, hB, hbound⟩ := rationalLatticeCoefficientDecay
    k G hG T i hi ν hν hStandard hU A hA hstrict K0 hBasis
  intro I _ _ J x hzero hpos hout
  obtain ⟨z, hz, hcoeff⟩ := hbound I J x hzero hpos hout
  refine ⟨z, hz, ?_⟩
  apply compactTranslateLatticeBound (RationalPoint k G.X) A A.representation A.isSmooth I
    (fun n => uniformizerPowers i (.ofAdd (∑ a, n a • x a)))
    (fun a => (((HaarModulus.closedRestrictCharacter (unipotent i ν (J a))
      (hU (J a)) (levi i ν (J a)) (levi_le_normalizer i ν (J a))
      (z a : levi i ν (J a)) : ℝ≥0) : ℝ))⁻¹)
  intro φ v
  obtain ⟨Kv, hv⟩ := A.isSmooth v
  obtain ⟨Kφ, hφ⟩ := φ.property
  obtain ⟨K, hKB, hKle⟩ := hB.2.mem_iff.mp (Kv ⊓ Kφ).mem_nhds_one
  let Ko : OpenSubgroup (RationalPoint k G.X) := ⟨K, (hB.1 K hKB).2.2.1⟩
  have hle : K ≤ Kv.toSubgroup ⊓ Kφ.toSubgroup := hKle
  have hvK : v ∈ fixedVectors A.representation K :=
    fixedVectors_antitone A.representation (le_trans hle inf_le_left) hv
  have hφK : (φ : Module.Dual ℂ A) ∈ fixedVectors A.representation.dual K :=
    fixedVectors_antitone A.representation.dual (le_trans hle inf_le_right) hφ
  exact hcoeff Ko hKB ⟨v, hvK⟩ (φ : Module.Dual ℂ A) hφK

end Langlands.Aubert.General.RationalPointFamily
