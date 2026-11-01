import Langlands.Representation.RankinSelberg.PadicPairFactors

/-! Constant-term normalization of p-adic pair L-polynomial certificates. -/

noncomputable section

namespace Langlands.RankinSelberg

open MeasureTheory HarmonicAnalysis Polynomial PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime]

section Normalization

variable {F : PadicField.{uF} p}
  {ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier}
  {ν : letI := F.canonicalTopologicalData.topology; letI := borel F.Carrier
    AdditiveHaarMeasure F.Carrier}
  {r t : ℕ} {V : Type uV} {W : Type uW}
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {π : Representation ℂ (Langlands.GeneralLinear (r + 1) F.Carrier) V}
  {σ : Representation ℂ (Langlands.GeneralLinear (t + 1) F.Carrier) W}
  {P : ℂ[X]}

/-- The p-adic relation inherits the normalization of its integral generator. -/
theorem IsPadicPairLPolynomial.coeff_zero (h : IsPadicPairLPolynomial F ψ ν π σ P) :
    P.coeff 0 = 1 := by
  let := F.canonicalTopologicalData.topology
  let := F.canonicalTopologicalData.valuativeRel
  let := F.canonicalTopologicalData.localField
  let := borel F.Carrier
  let : BorelSpace F.Carrier := ⟨rfl⟩
  let := borel (Langlands.GeneralLinear (t + 1) F.Carrier)
  let : BorelSpace (Langlands.GeneralLinear (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (GeneralLinear.upperUnipotent (t + 1) F.Carrier)
  let : BorelSpace (GeneralLinear.upperUnipotent (t + 1) F.Carrier) := ⟨rfl⟩
  let := borel (LeftUnipotentQuotient t F.Carrier)
  obtain ⟨⟨_, μ, hμ⟩, hP⟩ := h
  exact (hP μ hμ).coeff_zero

/-- Reading the larger rank first preserves the constant-term normalization. -/
theorem IsPadicSymmetricLPolynomial.coeff_zero
    (h : IsPadicSymmetricLPolynomial F ψ ν π σ P) : P.coeff 0 = 1 := by
  unfold IsPadicSymmetricLPolynomial at h
  split_ifs at h
  · exact h.coeff_zero
  · exact h.coeff_zero

end Normalization

end Langlands.RankinSelberg
