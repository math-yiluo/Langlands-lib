import Langlands.Representation.RankinSelberg.EpsilonGammaLaurentReduction
import Langlands.Representation.RankinSelberg.PadicPairFactors
import Langlands.Representation.Whittaker.ModelKirillovStatement
import Langlands.Representation.Whittaker.PrerequisiteInterfaces
import Langlands.Representation.Classification.SupercuspidalInverseTranspose
import Langlands.Representation.CompactCoefficient.GroupTransport

noncomputable section

namespace Langlands.Whittaker

open GeneralLinear HarmonicAnalysis RankinSelberg

universe uF uV

/-- The support half of supercuspidal Kirillov gives an actual mirabolic test
function for every vector in every nonzero-functional coefficient model. -/
theorem isMirabolicTestFunction_of_supercuspidalKirillov
    (hK : Langlands.SupercuspidalKirillovStatement.{uF, uV})
    {p : ℕ} [hp : Fact p.Prime] (F : PadicField.{uF} p) :
    letI := F.canonicalTopologicalData.topology
    ∀ (r : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
      (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (ψ : UnitaryAdditiveCharacter F.Carrier),
      GeneralLinear.IsSupercuspidal π → Representation.IsIrreducible π →
      ∀ (ℓ : glFunctionals ψ r π), ℓ.val ≠ 0 →
      ∀ f : (coefficientModel π ℓ).toSubmodule,
        IsMirabolicTestFunction ψ r f.val := by
  let := F.canonicalTopologicalData.topology
  intro r V _ _ π ψ hπ hi ℓ hℓ f
  have hψ : ψ.complex ≠ 1 := by
    intro hz
    apply ψ.nontrivial
    ext x
    exact DFunLike.congr_fun hz x
  have hcov : ∀ g : Langlands.GeneralLinear (r + 1) F.Carrier,
      ((∀ i j, j < i → g.val i j = 0) ∧ ∀ i, g.val i i = 1) →
      ∀ v, ℓ.val (π g v) =
        (∏ i : Fin r, ψ.complex (g.val i.castSucc i.succ)) * ℓ.val v := by
    intro g hg v
    exact (mem_glFunctionals_iff_entrywise ψ π ℓ.val).mp ℓ.property g hg.1 hg.2 v
  have h := (hK p hp F r V π ψ.complex ψ.continuous_complex hψ ψ.norm_complex
    hπ hi).2 ℓ.val hℓ hcov
  obtain ⟨v, hv⟩ := f.property
  have hf (g : Langlands.GeneralLinear (r + 1) F.Carrier) :
      f.val.val g = ℓ.val (π g v) := by
    rw [← hv]
    rfl
  obtain ⟨_, hsmooth, C, hC, hsupp⟩ := h.1 v
  refine ⟨?_, C, hC, ?_⟩
  · simpa only [hf] using hsmooth
  · intro q hq hne
    have hne' : ℓ.val (π q v) ≠ 0 := by simpa only [hf] using hne
    obtain ⟨u, c, hu, hc, heq⟩ := hsupp q hq hne'
    exact ⟨⟨u, hu⟩, c, hc, heq⟩

end Langlands.Whittaker

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance supercuspidalEpsilonGammaTopology : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalEpsilonGammaValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalEpsilonGammaLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supercuspidalEpsilonGammaFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance supercuspidalEpsilonGammaFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance supercuspidalEpsilonGammaGLMeasurable (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance supercuspidalEpsilonGammaGLBorel (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance supercuspidalEpsilonGammaUnipotentMeasurable (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance supercuspidalEpsilonGammaUnipotentBorel (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance supercuspidalEpsilonGammaQuotientMeasurable (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _

variable {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ψ : UnitaryAdditiveCharacter F.Carrier} {ν : AdditiveHaarMeasure F.Carrier}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}

/-- Block-zero rational values in the canonical p-adic coefficient models are
Laurent polynomials, for every compatible quotient measure and nonzero pair of
functionals. This does not assert that the rational values exist. -/
def PadicBlockZeroLaurentValues (hnr : n < r)
    (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier)
    (π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W) : Prop :=
  ∀ (μ : Measure (LeftUnipotentQuotient n F.Carrier)),
    IsCompatible (upperUnipotent (n + 1) F.Carrier) (generalLinearHaar F.Carrier n)
      (unipotentHaar F.Carrier n) μ →
    ∀ (ℓ : glFunctionals ψ r π) (ℓ' : glInverseFunctionals ψ n σ),
      ℓ.val ≠ 0 → ℓ'.val ≠ 0 →
      HasLaurentValues (unequalRankValuesAt 0 (r - n - 1) (by omega)
        F.canonicalTopologicalData.residueCardinality ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData) μ
        (rectangularMeasure ν 0 (n + 1)) π σ ℓ ℓ')

/-- Canonical p-adic specialization of the block-zero Laurent reduction. -/
theorem IsPadicPairEpsilonFactor.gammaFactor_of_laurentValues (hnr : n < r)
    (hL : PadicBlockZeroLaurentValues hnr ψ ν π σ)
    (hLd : PadicBlockZeroLaurentValues hnr (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ))
    {e : ℂˣ × ℤ} (hε : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    IsPadicPairGammaFactor F ψ ν π σ
      (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) := by
  change IsPairGammaFactor _ _ _ _ _ _ _
  rw [isPairGammaFactor_of_lt hnr]
  have hε' := (isPairEpsilonFactor_of_lt hnr).mp hε
  refine hε'.gammaFactor_of_laurentValues hnr
    F.canonicalTopologicalData.residueCardinality_gt_one hL ?_
  intro μ hμ ℓ ℓ' hℓ hℓ'
  exact hLd μ hμ _ _ (firstDualFunctional_ne_zero ψ π hℓ)
    (secondDualFunctional_ne_zero ψ σ hℓ')

/-- Supercuspidal Kirillov and a block-zero Laurent theorem for mirabolic tests
imply the epsilon-monomial gamma relation. The smaller input needs only
smoothness. Both analytic inputs are explicit. -/
theorem IsPadicPairEpsilonFactor.gammaFactor_of_supercuspidalKirillov
    (hnr : n < r) (hK : Langlands.SupercuspidalKirillovStatement.{uF, uV})
    (hLaurent : ∀ (Ψ : UnitaryAdditiveCharacter F.Carrier)
      (ρ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
      (τ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W),
      IsSmooth τ →
      (∀ (ℓ : glFunctionals Ψ r ρ), ℓ.val ≠ 0 →
        ∀ f : (coefficientModel ρ ℓ).toSubmodule,
          IsMirabolicTestFunction Ψ r f.val) →
      PadicBlockZeroLaurentValues hnr Ψ ν ρ τ)
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hσ : IsSmooth σ) {e : ℂˣ × ℤ}
    (hε : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    IsPadicPairGammaFactor F ψ ν π σ
      (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) := by
  have hL : PadicBlockZeroLaurentValues hnr ψ ν π σ :=
    hLaurent ψ π σ hσ
      (isMirabolicTestFunction_of_supercuspidalKirillov hK F r V π ψ hπ hirr)
  have hπd : GeneralLinear.IsSupercuspidal (inverseTransposePullback π) :=
    GeneralLinear.isSupercuspidal_comp_inverseTranspose π hπ
  have hird : Representation.IsIrreducible (inverseTransposePullback π) :=
    (isIrreducible_comp_continuousMulEquiv_iff π
      (inverseTransposeContinuous (r + 1) F.Carrier)).mpr hirr
  have hLd : PadicBlockZeroLaurentValues hnr (ψ.scale (-1)) ν
      (inverseTransposePullback π) (inverseTransposePullback σ) :=
    hLaurent (ψ.scale (-1)) (inverseTransposePullback π) (inverseTransposePullback σ)
      (inverseTransposePullback_isSmooth σ hσ)
      (isMirabolicTestFunction_of_supercuspidalKirillov hK F r V
        (inverseTransposePullback π) (ψ.scale (-1)) hπd hird)
  exact hε.gammaFactor_of_laurentValues hnr hL hLd

end Langlands.RankinSelberg
