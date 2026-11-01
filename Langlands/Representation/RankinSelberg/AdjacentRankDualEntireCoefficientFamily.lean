import Langlands.Representation.RankinSelberg.AdjacentRankEntireCoefficientSpecialization
import Langlands.Representation.RankinSelberg.DualModels
import Langlands.Representation.RankinSelberg.DualWhittakerType

/-! Entire determinant-slice coefficients for the actual Weyl-translated dual family. -/

noncomputable section

namespace Langlands.RankinSelberg.Padic

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear QuotientIntegration
open ParameterSpecialization

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance dualEntireTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology
local instance dualEntireValuation : ValuativeRel F.Carrier :=
  F.canonicalTopologicalData.valuativeRel
local instance dualEntireLocalField : IsNonarchimedeanLocalField F.Carrier :=
  F.canonicalTopologicalData.localField
local instance dualEntireFieldMeasurable : MeasurableSpace F.Carrier := borel _
local instance dualEntireFieldBorel : BorelSpace F.Carrier := ⟨rfl⟩
local instance dualEntireGroupMeasurable (r : ℕ) :
    MeasurableSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := borel _
local instance dualEntireGroupBorel (r : ℕ) :
    BorelSpace (Langlands.GeneralLinear (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualEntireUnipotentMeasurable (r : ℕ) :
    MeasurableSpace (upperUnipotent (r + 1) F.Carrier) := borel _
local instance dualEntireUnipotentBorel (r : ℕ) :
    BorelSpace (upperUnipotent (r + 1) F.Carrier) := ⟨rfl⟩
local instance dualEntireQuotientMeasurable (r : ℕ) :
    MeasurableSpace (LeftUnipotentQuotient r F.Carrier) := borel _
local instance dualEntireQuotientBorel (r : ℕ) :
    BorelSpace (LeftUnipotentQuotient r F.Carrier) := ⟨rfl⟩

/-- A fixed right translation conjugates one common compact open level. -/
theorem HasCommonCompactOpenRightLevel.translate
    {r : ℕ} {ψ : UnitaryAdditiveCharacter F.Carrier}
    {U : ℂ → WhittakerFunctions ψ r}
    (hU : HasCommonCompactOpenRightLevel F U)
    (a : Langlands.GeneralLinear (r + 1) F.Carrier) :
    HasCommonCompactOpenRightLevel F (fun z => translateWhittaker ψ r (U z) a) := by
  obtain ⟨K, hKo, hKc, hK⟩ := hU
  let e : Langlands.GeneralLinear (r + 1) F.Carrier ≃ₜ
      Langlands.GeneralLinear (r + 1) F.Carrier :=
    (Homeomorph.mulLeft a⁻¹).trans (Homeomorph.mulRight a)
  let L := K.comap (MulAut.conj a⁻¹).toMonoidHom
  have hL : (L : Set (Langlands.GeneralLinear (r + 1) F.Carrier)) = e ⁻¹' K := by
    ext k
    simp [L, e]
  refine ⟨L, ?_, ?_, ?_⟩
  · rw [hL]
    exact e.isOpen_preimage.mpr hKo
  · rw [hL]
    exact e.isCompact_preimage.mpr hKc
  · intro z g k
    have hk : a⁻¹ * k.val * a ∈ K := by
      have hk' := k.property
      change a⁻¹ * k.val * (a⁻¹)⁻¹ ∈ K at hk'
      simpa only [inv_inv] using hk'
    change (U z).val ((g * k.val) * a) = (U z).val (g * a)
    have heq : (g * k.val) * a = (g * a) * (a⁻¹ * k.val * a) := by
      simp only [mul_assoc, mul_inv_cancel_left]
    rw [heq]
    exact hK z (g * a) ⟨_, hk⟩

/-- Inverse transpose pulls one common compact open level back to a common
compact open level for the actual first dual functions. -/
theorem HasCommonCompactOpenRightLevel.firstDual
    {r : ℕ} {ψ : UnitaryAdditiveCharacter F.Carrier}
    {U : ℂ → WhittakerFunctions ψ r}
    (hU : HasCommonCompactOpenRightLevel F U) :
    HasCommonCompactOpenRightLevel F (fun z => firstDualFunction ψ r (U z)) := by
  obtain ⟨K, hKo, hKc, hK⟩ := hU
  let e := inverseTransposeContinuous (r + 1) F.Carrier
  let L := K.comap e.toMonoidHom
  refine ⟨L, e.toHomeomorph.isOpen_preimage.mpr hKo,
    e.toHomeomorph.isCompact_preimage.mpr hKc, ?_⟩
  intro z g k
  change (U z).val (weylLong (r + 1) F.Carrier *
      inverseTranspose (r + 1) F.Carrier (g * k.val)) =
    (U z).val (weylLong (r + 1) F.Carrier *
      inverseTranspose (r + 1) F.Carrier g)
  rw [map_mul, ← mul_assoc]
  exact hK z _ ⟨e k.val, k.property⟩

/-- The actual first dual transform, followed by the block Weyl translation
in the adjacent functional equation. -/
def adjacentRankDualWhittakerFamily
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) :
    ℂ → WhittakerFunctions (ψ.scale (-1)) (r + 1) :=
  fun z => translateWhittaker (ψ.scale (-1)) (r + 1)
    (firstDualFunction ψ (r + 1) (U z))
    (blockWeylAt r (r + 1) (Nat.lt_succ_self r))

/-- The actual translated dual family retains a common compact open right
level and pointwise entire parameter dependence. -/
theorem adjacentRankDualWhittakerFamily_level_entire
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g z, AnalyticAt ℂ (fun u => (U u).val g) z) :
    HasCommonCompactOpenRightLevel F (adjacentRankDualWhittakerFamily F ψ r U) ∧
      ∀ g z, AnalyticAt ℂ
        (fun u => (adjacentRankDualWhittakerFamily F ψ r U u).val g) z := by
  refine ⟨(hK.firstDual F).translate F _, ?_⟩
  intro g z
  exact hU _ z

/-- The literal coefficients of the actual adjacent dual integral at spectral
parameter zero, for the same original test model vector. -/
def adjacentRankDualCoefficientFamily {r : ℕ}
    (ψ : UnitaryAdditiveCharacter F.Carrier)
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (Wprime : InverseWhittakerFunctions ψ r)
    (U : ℂ → WhittakerFunctions ψ (r + 1)) : ℂ → BilateralLaurentSeries :=
  corankCoefficientFamily F (ψ.scale (-1)) ν
    (secondDualFunction ψ r Wprime) (adjacentRankDualWhittakerFamily F ψ r U)

/-- The published corank slice theorem applies to the actual dual test model
and actual translated dual family, giving both integrability and entire
dependence of every literal dual determinant-slice coefficient. -/
theorem adjacentRankDualCoefficientFamily_integrable_entire
    (ψ : UnitaryAdditiveCharacter F.Carrier) (r : ℕ)
    [Measure.IsMulRightInvariant (unipotentHaar F.Carrier r)]
    (ν : Measure (LeftUnipotentQuotient r F.Carrier))
    (hν : IsCompatible (upperUnipotent (r + 1) F.Carrier)
      (generalLinearHaar F.Carrier r) (unipotentHaar F.Carrier r) ν)
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (τ : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V)
    (hτ : IsOfWhittakerType r (inverseStandardCharacter ψ r) τ)
    (ℓ : glInverseFunctionals ψ r τ)
    (Wprime : (coefficientModel τ ℓ).toSubmodule)
    (U : ℂ → WhittakerFunctions ψ (r + 1))
    (hK : HasCommonCompactOpenRightLevel F U)
    (hU : ∀ g z, AnalyticAt ℂ (fun u => (U u).val g) z) :
    (∀ z, SliceIntegrable F.canonicalTopologicalData ν
      (corankOneIntegrand (ψ.scale (-1))
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (adjacentRankDualWhittakerFamily F ψ r U z)
        (secondDualFunction ψ r Wprime.val) 0)) ∧
      EntireCoefficientFamily (adjacentRankDualCoefficientFamily F ψ ν Wprime.val U) := by
  have hτd : IsOfWhittakerType r
      (inverseStandardCharacter (ψ.scale (-1)) r) (inverseTransposePullback τ) := by
    simpa only [inverseStandardCharacter_scale_neg_one] using
      isOfWhittakerType_inverseTransposePullback_inverse ψ τ hτ
  obtain ⟨hKd, hUd⟩ := adjacentRankDualWhittakerFamily_level_entire F ψ r U hK hU
  exact corankCoefficientFamily_integrable_entire F (ψ.scale (-1)) r ν hν
    (inverseTransposePullback τ) hτd (secondDualFunctional ψ τ ℓ)
    (secondDualModelMap ψ τ ℓ Wprime) (adjacentRankDualWhittakerFamily F ψ r U)
    hKd hUd

end Langlands.RankinSelberg.Padic
