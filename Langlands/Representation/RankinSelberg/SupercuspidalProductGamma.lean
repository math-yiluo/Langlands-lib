import Langlands.Representation.RankinSelberg.SupercuspidalEpsilonGammaReduction
import Langlands.Representation.RankinSelberg.SupercuspidalZeroBlockLaurent
import Langlands.Representation.RankinSelberg.GenericModel
import Langlands.Representation.RankinSelberg.GammaMultiplicativityProof

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance supercuspidalProductGammaTopologicalSpace : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalProductGammaValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalProductGammaIsNonarchimedeanLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supercuspidalProductGammaMeasurableSpace : MeasurableSpace F.Carrier := borel _
local instance supercuspidalProductGammaBorelSpace : BorelSpace F.Carrier := ⟨rfl⟩
local instance supercuspidalProductGammaMeasurableSpace2 (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := borel _
local instance supercuspidalProductGammaBorelSpace2 (n : ℕ) : BorelSpace (Langlands.GeneralLinear (n + 1) F.Carrier) := ⟨rfl⟩
local instance supercuspidalProductGammaMeasurableSpace3 (n : ℕ) : MeasurableSpace (upperUnipotent (n + 1) F.Carrier) := borel _
local instance supercuspidalProductGammaBorelSpace3 (n : ℕ) : BorelSpace (upperUnipotent (n + 1) F.Carrier) := ⟨rfl⟩
local instance supercuspidalProductGammaMeasurableSpace4 (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) := borel _

section EpsilonGamma

variable {r n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {ψ : UnitaryAdditiveCharacter F.Carrier} {ν : AdditiveHaarMeasure F.Carrier}
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}

/-- For a supercuspidal larger representation the block-zero Laurent premise
is discharged. Only the supercuspidal Kirillov theorem remains an input. -/
theorem IsPadicPairEpsilonFactor.gammaFactor_of_supercuspidal
    (hnr : n < r) (hK : Langlands.SupercuspidalKirillovStatement.{uF, uV})
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hσ : IsSmooth σ) {e : ℂˣ × ℤ}
    (hε : IsPadicPairEpsilonFactor F ψ ν π σ e) :
    IsPadicPairGammaFactor F ψ ν π σ
      (rationalEpsilonMonomial e.1 e.2 : RationalFunctions) := by
  apply hε.gammaFactor_of_supercuspidalKirillov hnr hK _ hπ hirr hσ
  intro Ψ ρ τ hτ hρ μ hμ ℓ ℓ' hℓ _
  have := hμ.regular
  exact exists_laurent_of_mem_unequalRankValuesAt_zero F (r - n - 1) (by omega)
    Ψ ν μ ρ τ hτ ℓ ℓ' (hρ ℓ hℓ)

/-- The existence clause in supercuspidal Kirillov supplies genericity;
published multiplicity one then supplies full Whittaker type. -/
theorem isOfWhittakerType_of_supercuspidalKirillov
    (hK : Langlands.SupercuspidalKirillovStatement.{uF, uV})
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π) :
    IsOfWhittakerType r (standardCharacter ψ r) π := by
  have hψ : ψ.complex ≠ 1 := by
    intro hz
    apply ψ.nontrivial
    ext x
    exact DFunLike.congr_fun hz x
  obtain ⟨ℓ, hℓ, hcov⟩ :=
    (hK p inferInstance F r V π ψ.complex ψ.continuous_complex hψ ψ.norm_complex hπ hirr).1
  have hL : ℓ ∈ glFunctionals ψ r π := by
    apply (mem_glFunctionals_iff_entrywise ψ π ℓ).mpr
    intro g hlow hdiag v
    exact hcov g ⟨hlow, hdiag⟩ v
  exact isOfWhittakerType_of_isGeneric F ⟨hirr, hπ.1, ⟨⟨ℓ, hL⟩, hℓ⟩⟩

end EpsilonGamma

/-- Common gamma factors against every normalized ordered product of
supercuspidal representations of total rank `k+1`. The larger inputs have
rank `k+2`, and the block carriers all lie in the specified universe `uW`. -/
def SameProductGammaFactors
    (F : PadicField.{uF} p)
    (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
    (ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
      AdditiveHaarMeasure F.Carrier) (k : ℕ)
    {V V' : Type uV} [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    (π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V)
    (π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V') : Prop :=
  ∀ (b : ℕ) (m : Fin b → ℕ) (h : ∑ i, (m i + 1) = k + 1)
    (τ : ∀ i, letI := F.canonicalTopologicalData.topology
      GeneralLinear.SupercuspidalRep.{uF, uW} (F := F.Carrier) (n := m i + 1)),
    ∃ G : RationalFunctions,
      IsPadicPairGammaFactor F ψ ν π
        (F.canonicalNormalizedProductInduced (succBlockShape m h)
          (fun i => (τ i).obj.representation)) G ∧
      IsPadicPairGammaFactor F ψ ν π'
        (F.canonicalNormalizedProductInduced (succBlockShape m h)
          (fun i => (τ i).obj.representation)) G

/-- Common supercuspidal epsilon factors extend to common gamma factors
against normalized products, using the proved gamma multiplicativity theorem.
The Kirillov input is required at both original carrier universes. -/
theorem SameSupercuspidalEpsilonFactors.productGammaFactors
    (hKV : Langlands.SupercuspidalKirillovStatement.{uF, uV})
    (hKW : Langlands.SupercuspidalKirillovStatement.{uF, uW})
    {ψ : UnitaryAdditiveCharacter F.Carrier}
    (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
    {k : ℕ} {V V' : Type uV}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup V'] [Module ℂ V']
    {π : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V}
    {π' : Representation ℂ (Langlands.GeneralLinear (k + 1 + 1) F.Carrier) V'}
    (hπ : GeneralLinear.IsSupercuspidal π) (hirr : Representation.IsIrreducible π)
    (hπ' : GeneralLinear.IsSupercuspidal π') (hirr' : Representation.IsIrreducible π')
    (hSame : SameSupercuspidalEpsilonFactors.{uF, uV, uW} F ψ ν.val k π π') :
    SameProductGammaFactors.{uF, uV, uW} F ψ ν.val k π π' := by
  intro b m h τ
  have htype := isOfWhittakerType_of_supercuspidalKirillov (ψ := ψ) hKV hπ hirr
  have htype' := isOfWhittakerType_of_supercuspidalKirillov (ψ := ψ) hKV hπ' hirr'
  have htypes : ∀ i, IsOfWhittakerType (m i) (standardCharacter ψ (m i))
      (τ i).obj.representation :=
    fun i => isOfWhittakerType_of_supercuspidalKirillov hKW (τ i).property.2
      (τ i).property.1
  obtain ⟨G, hG, hI⟩ := gammaMultiplicativity p F ψ ν (k + 1) k b m h
    π (fun i => (τ i).obj.representation) htype htypes
  obtain ⟨G', hG', hI'⟩ := gammaMultiplicativity p F ψ ν (k + 1) k b m h
    π' (fun i => (τ i).obj.representation) htype' htypes
  have heq : G = G' := by
    funext i
    have hle : m i + 1 ≤ ∑ j, (m j + 1) :=
      Finset.single_le_sum (fun j _ => Nat.zero_le (m j + 1)) (Finset.mem_univ i)
    rw [h] at hle
    have hmi : m i ≤ k := by omega
    have hlt : m i < k + 1 := by omega
    obtain ⟨e, he, he'⟩ := hSame (m i) hmi (τ i)
    have hγ := he.gammaFactor_of_supercuspidal hlt hKV hπ hirr (τ i).obj.isSmooth
    have hγ' := he'.gammaFactor_of_supercuspidal hlt hKV hπ' hirr' (τ i).obj.isSmooth
    exact ((isPadicSymmetricGammaFactor_of_le hlt.le).mp (hG i)).unique hγ |>.trans
      (((isPadicSymmetricGammaFactor_of_le hlt.le).mp (hG' i)).unique hγ').symm
  refine ⟨∏ i, G i, (isPadicSymmetricGammaFactor_of_le (by omega)).mp hI, ?_⟩
  rw [heq]
  exact (isPadicSymmetricGammaFactor_of_le (by omega)).mp hI'

end Langlands.RankinSelberg
