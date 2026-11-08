import Langlands.Representation.RankinSelberg.SupercuspidalEqualRankLaurent
import Langlands.Representation.RankinSelberg.TwistedPositiveIntegral
import Langlands.Representation.RankinSelberg.CentralRowShell

/-! # Compact and positive supercuspidal row integrals -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Whittaker GeneralLinear

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

local instance supercuspidalRowIntegralsTopologicalSpace : TopologicalSpace F.Carrier := F.canonicalTopologicalData.topology
local instance supercuspidalRowIntegralsValuativeRel : ValuativeRel F.Carrier := F.canonicalTopologicalData.valuativeRel
local instance supercuspidalRowIntegralsIsNonarchimedeanLocalField : IsNonarchimedeanLocalField F.Carrier := F.canonicalTopologicalData.localField
local instance supercuspidalRowIntegralsT2Space : T2Space F.Carrier := F.canonicalTopologicalData.fieldT2

variable {n : ℕ} {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (n + 1) F.Carrier) W}
  {ψ : UnitaryAdditiveCharacter F.Carrier} {ℓ : glFunctionals ψ n π}

/-- Every zero-row test gives compact support of the actual quotient integrand,
for all first vectors, inverse Whittaker functions, and spectral parameters. -/
def HasCompactSupercuspidalRowIntegrands : Prop :=
  ∀ (v : V) (W' : InverseWhittakerFunctions ψ n)
    (Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier)), Φ 0 = 0 → ∀ s : ℂ,
      HasCompactSupport (equalRankIntegrand ψ
        (normalizedAbsoluteValue F.canonicalTopologicalData)
        (coefficientMap π ℓ v) W' Φ s)

/-- The full Kirillov support statement and smooth coefficient stabilizers
supply actual compact quotient support for all zero-row tests. -/
theorem hasCompactSupercuspidalRowIntegrands_of_kirillov
    (hK : SupercuspidalKirillovStatement.{uF,uV})
    (hπ : IsSupercuspidal π) (hiπ : π.IsIrreducible) (hℓ : ℓ.val ≠ 0) :
    HasCompactSupercuspidalRowIntegrands (π := π) (ℓ := ℓ) := by
  intro v W' Φ hΦ s
  have hmir := hasMirabolicCompactTranslates_of_supercuspidalKirillov hK hπ hiπ hℓ v
  obtain ⟨J, hJ, hfix⟩ := exists_compact_open_coefficient_stabilizer (ℓ := ℓ) hπ.1.1 v
  exact hmir.equalRankIntegrand_hasCompactSupport J hJ hfix W' Φ hΦ _ s

local instance rowQuotientMeasurable : MeasurableSpace (LeftUnipotentQuotient n F.Carrier) :=
  borel _
local instance rowQuotientBorel : BorelSpace (LeftUnipotentQuotient n F.Carrier) := ⟨rfl⟩

/-- The positive central shell has a convergent strictly positive integral once
the compact-support and weighted squared-norm coefficient inputs are supplied. -/
theorem HasPadicTwistedPositiveCoefficients.exists_positive_central_shell_integral
    {μ : Measure (LeftUnipotentQuotient n F.Carrier)} {u : ℂ}
    (h : HasPadicTwistedPositiveCoefficients F.canonicalTopologicalData π σ ψ u ℓ)
    (hℓ : ℓ.val ≠ 0)
    (hc : HasCompactSupercuspidalRowIntegrands (π := π) (ℓ := ℓ))
    (hμ : μ.IsOpenPosMeasure) (hμc : IsFiniteMeasureOnCompacts μ)
    (hπ : IsSmooth π) (hσ : IsSmooth σ) :
    ∃ Φ : SchwartzBruhat (Fin (n + 1) → F.Carrier), Φ 0 = 1 ∧
      let Ψ := Φ - rowTranslate (centralSpectralElement F.canonicalTopologicalData (n + 1)) Φ
      Ψ 0 = 0 ∧ HasPositiveEqualRankIntegral F.canonicalTopologicalData π σ ψ μ u ℓ Ψ := by
  obtain ⟨Φ, hΦ, hΨ0, hΨ1, hΨ⟩ := hasPositiveCentralRowShell F.canonicalTopologicalData n
  refine ⟨Φ, hΦ, hΨ0, ?_⟩
  exact h.hasPositiveEqualRankIntegral_of_compactSupport F.canonicalTopologicalData π σ
    hℓ hμ hμc hπ hσ _ hΨ1 hΨ (fun m v w => hc v (coefficientMap σ m w) _ hΨ0 (-u))

end Langlands.RankinSelberg
