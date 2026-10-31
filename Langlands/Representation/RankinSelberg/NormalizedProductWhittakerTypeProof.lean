import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeStatement
import Langlands.Representation.RankinSelberg.WhittakerTypeTwist
import Langlands.Representation.RankinSelberg.WhittakerTypeEquivalence
import Langlands.Representation.Induction.BlockCharacterAbsorption
import Langlands.Representation.Parabolic.NormalizedAdmissibilityProof
import Langlands.Representation.Tensor.FiniteProperties
import Langlands.Representation.Whittaker.InducedWhittakerTypeProof
import Langlands.Representation.Whittaker.InducedFiniteTypeProof
import Langlands.Representation.Whittaker.FunctionalLine

/-! # Full Whittaker type of normalized upper block induction -/

namespace Langlands.RankinSelberg

open HarmonicAnalysis Whittaker GeneralLinear

universe uF uW

/-- Actual normalized upper block induction preserves all three clauses of full
Whittaker type for arbitrary full-type blocks. -/
theorem normalizedProductWhittakerType :
    NormalizedProductWhittakerTypeStatement.{uF, uW} := by
  intro p hp F ψ t k m h W _ _ σ hσ
  let T := F.canonicalTopologicalData
  let := T.topology
  let := T.generalLinearTopologicalGroup (t + 1)
  let B := succBlockShape m h
  let τ := T.blockHalfTwist B σ
  have hτ : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (τ i) := by
    intro i
    exact (isOfWhittakerType_twist_iff (standardCharacter ψ (m i))
      (T.blockHalfModulus B i) (σ i) (T.isOpen_ker_blockHalfModulus B i)
      (T.blockHalfModulus_upperUnipotent B i)).mpr (hσ i)
  have hadm : IsAdmissible (F.canonicalNormalizedProductInduced B σ) :=
    Parabolic.normalizedInductionAdmissibility F T B _ (B.blockTensor σ)
      (FiniteTensor.isAdmissible_external σ (fun i => (hσ i).1))
  have hfinite := Langlands.inducedFiniteType.{uF, uW} p hp F t B W τ (fun i => (hτ i).1)
    (fun i => (hτ i).2.1)
  have hne : ψ.complex ≠ 1 := by
    intro he
    apply ψ.nontrivial
    ext x
    exact congrArg (fun χ : AddChar F.Carrier ℂ => χ x) he
  have hraw := (Langlands.inducedWhittakerType.{uF, uW}
    p hp F t B W τ ψ.complex ψ.continuous_complex hne
    ψ.norm_complex (fun i => (hτ i).1) (fun i => (hτ i).2.1)).mpr
    (fun i => (nonempty_standardFunctionalsEquiv_iff ψ (m i) (τ i)).mp (hτ i).2.2)
  have hline := (nonempty_standardFunctionalsEquiv_iff ψ t
    (Induction.smoothInduced (B.parabolic F.Carrier)
      ((B.blockTensor τ).comp (B.leviProjection F.Carrier)))).mpr hraw
  let e := T.normalizedProductHalfAbsorptionEquiv B σ
  refine ⟨hadm, (finite_asModule_iff_of_equiv e).mpr hfinite, ?_⟩
  obtain ⟨l⟩ := hline
  exact ⟨(Whittaker.functionalsCongr e).trans l⟩

end Langlands.RankinSelberg
