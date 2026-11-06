import Langlands.Representation.RankinSelberg.TemperedLFactorStatement
import Langlands.Representation.RankinSelberg.PadicPairLFactor
import Langlands.Representation.RankinSelberg.SupercuspidalEpsilonGammaReduction
import Langlands.Representation.RankinSelberg.SupercuspidalZeroBlockLaurent
import Langlands.Representation.Whittaker.SupercuspidalKirillovProof

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

/-- JPSS (8.1)(i) follows from the supercuspidal Kirillov theorem. -/
theorem supercuspidalUnequalRankLFactor_of_kirillov
    (hK : Langlands.SupercuspidalKirillovStatement.{uF, uV}) :
    SupercuspidalUnequalRankLFactorStatement.{uF, uV, uW} := by
  intro p hp F ψ ν r t V _ _ W _ _ π σ hi hsc hσ htr
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := F.canonicalTopologicalData.secondCountableTopology
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  let : BorelSpace (LeftUnipotentQuotient t F.Carrier) := ⟨rfl⟩
  have hψ : ψ.complex ≠ 1 := by
    intro hz
    apply ψ.nontrivial
    ext x
    exact DFunLike.congr_fun hz x
  obtain ⟨ℓ₀, hℓ₀, hcov⟩ :=
    (hK p hp F r V π ψ.complex ψ.continuous_complex hψ ψ.norm_complex hsc hi).1
  have hmem : ℓ₀ ∈ glFunctionals ψ r π := by
    apply (mem_glFunctionals_iff_entrywise ψ π ℓ₀).mpr
    intro g hu hd v
    exact hcov g ⟨hu, hd⟩ v
  let ℓ : glFunctionals ψ r π := ⟨ℓ₀, hmem⟩
  have hℓ : ℓ.val ≠ 0 := hℓ₀
  have hπ : IsOfWhittakerType r (standardCharacter ψ r) π :=
    isOfWhittakerType_of_isGeneric F ⟨hi, hsc.1, ℓ, hℓ⟩
  have hσi : IsOfWhittakerType t (inverseStandardCharacter ψ t) σ :=
    (isOfWhittakerType_standard_iff_inverse ψ σ).mp hσ
  obtain ⟨ℓ', hℓ'⟩ := hσi.exists_ne_zero
  refine ⟨⟨inferInstance, unipotent_compatibleMeasureExists F.Carrier t⟩, ?_⟩
  intro _ μ hμ
  let := hμ.regular
  obtain ⟨P, hP⟩ :=
    unequalRankCommonGenerator.{uF, uV, uW} F F.canonicalTopologicalData t r
      htr ψ μ hμ ν.val V W π σ hπ hσi ℓ ℓ' hℓ hℓ'
  have hLaurent :
      HasLaurentValues (unequalRankValuesAt 0 (r - t - 1) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (rectangularMeasure ν.val 0 (t + 1)) π σ ℓ ℓ') :=
    exists_laurent_of_mem_unequalRankValuesAt_zero F (r - t - 1) (by omega)
      ψ ν.val μ π σ hσ.1.1 ℓ ℓ'
      (isMirabolicTestFunction_of_supercuspidalKirillov hK F r V π ψ hsc hi ℓ hℓ)
  have hPone : P = 1 :=
    (hP 0 (r - t - 1) (by omega)).eq_one_of_laurentValues hLaurent
  subst P
  apply (isPairLPolynomial_of_lt htr).2
  intro j k hr
  have hPj := hP j k hr
  subst r
  rw [unequalRankZetaValuesAt_rfl,
    (unequalRankAnalytic.{uF, uV, uW} F F.canonicalTopologicalData t j k
      ψ μ hμ ν.val V W π σ hπ hσi ℓ ℓ' hℓ hℓ').zetaValues_eq hπ hσi hℓ hℓ']
  exact hPj

/-- JPSS (8.1)(i): the pair L-factor of a supercuspidal representation
against a representation of Whittaker type of smaller rank is `1`. -/
theorem supercuspidalUnequalRankLFactor :
    SupercuspidalUnequalRankLFactorStatement.{uF, uV, uW} :=
  supercuspidalUnequalRankLFactor_of_kirillov Langlands.supercuspidalKirillov

end Langlands.RankinSelberg
