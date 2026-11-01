import Langlands.Representation.RankinSelberg.TwoBlockDominantRankTransport
import Langlands.Representation.RankinSelberg.NormalizedProductWhittakerTypeProof
import Langlands.Representation.RankinSelberg.WhittakerTypeGammaConstructionInputProof
import Langlands.Representation.RankinSelberg.SymmetricLPolynomialExistenceProof

/-!
# Factor existence for the dominant-rank assembly

Published full-type preservation and the general pair analytic theorems supply
the individual certificates. No multiplicative comparison is asserted here.
-/

noncomputable section

namespace Langlands.RankinSelberg.DominantRankTransport

open GeneralLinear HarmonicAnalysis MeasureTheory Polynomial Whittaker

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
  (ψ : letI := F.canonicalTopologicalData.topology; UnitaryAdditiveCharacter F.Carrier)
  (ν : LocalFactor.PadicAbelian.SelfDualHaar F.canonicalTopologicalData ψ)
  {r t : ℕ} (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Fin 2 → Type uW} [∀ i, AddCommGroup (W i)] [∀ i, Module ℂ (W i)]
  (π : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V)
  (σ : ∀ i, Representation ℂ (GeneralLinear (m i + 1) F.Carrier) (W i))
  (hπ : letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType r (standardCharacter ψ r) π)
  (hσ : ∀ i, letI := F.canonicalTopologicalData.topology;
    IsOfWhittakerType (m i) (standardCharacter ψ (m i)) (σ i))

include hπ hσ

/-- All individual gamma certificates for the actual upper induction and the
blocks exist before any product comparison. No rank inequality is required. -/
theorem upperGammaFactorsExist :
    ∃ (G : RationalFunctions) (Gi : Fin 2 → RationalFunctions),
      IsPadicSymmetricGammaFactor F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) G ∧
      ∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (Gi i) := by
  have hInd := normalizedProductWhittakerType p F ψ t 2 m h σ hσ
  let g := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π
    (F.canonicalNormalizedProductInduced (succBlockShape m h) σ)
    (whittakerTypeGammaConstructionInput p F ψ ν r t _ _
      π (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) hπ hInd)
  let gi (i : Fin 2) := padicSymmetricGammaFactorOfWhittakerType F ψ ν.val π (σ i)
    (whittakerTypeGammaConstructionInput p F ψ ν r (m i) V (W i)
      π (σ i) hπ (hσ i))
  exact ⟨(g.val : RationalFunctions), fun i => (gi i).val, g.property,
    fun i => (gi i).property⟩

/-- All individual L-polynomial certificates for the actual upper induction and
the blocks exist before any divisibility comparison. -/
theorem upperLPolynomialsExist :
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
      ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i) := by
  have hInd := normalizedProductWhittakerType p F ψ t 2 m h σ hσ
  obtain ⟨P, hP⟩ := symmetricLPolynomialExists p F ψ ν r t _ _
    π (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) hπ hInd
  have hi : ∀ i, ∃ Pi : ℂ[X], IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) Pi :=
    fun i => symmetricLPolynomialExists p F ψ ν r (m i) V (W i)
      π (σ i) hπ (hσ i)
  choose Pi hPi using hi
  exact ⟨P, Pi, hP, hPi⟩

/-- The same individual gamma certificates exist for the actual lower
induction with the entire dependent block family reversed. -/
theorem lowerReversedGammaFactorsExist :
    ∃ (G : RationalFunctions) (Gi : Fin 2 → RationalFunctions),
      IsPadicSymmetricGammaFactor F ψ ν.val π (lowerReversed F m h σ) G ∧
      ∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i.rev) (Gi i) := by
  obtain ⟨G, Gi, hG, hGi⟩ := upperGammaFactorsExist F ψ ν m h π σ hπ hσ
  obtain ⟨E⟩ := lowerReversedToUpperEquiv F m h σ (fun i => (hσ i).1.1)
  exact ⟨G, fun i => Gi i.rev,
    (IsPadicSymmetricGammaFactor.congr_equiv
      (Representation.Equiv.refl π) E).2 hG,
    fun i => hGi i.rev⟩

/-- Actual lower induction also has individual L-polynomial certificates,
without claiming the polynomial divisibility needed by the target. -/
theorem lowerReversedLPolynomialsExist :
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π (lowerReversed F m h σ) P ∧
      ∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i.rev) (Pi i) := by
  obtain ⟨P, Pi, hP, hPi⟩ := upperLPolynomialsExist F ψ ν m h π σ hπ hσ
  obtain ⟨E⟩ := lowerReversedToUpperEquiv F m h σ (fun i => (hσ i).1.1)
  exact ⟨P, fun i => Pi i.rev,
    (IsPadicSymmetricLPolynomial.congr_equiv
      (Representation.Equiv.refl π) E).2 hP,
    fun i => hPi i.rev⟩

/-- Once the actual lower gamma comparison is supplied, the published existence
theorems and actual representation transport give the upper conclusion. -/
theorem gammaConclusion_of_lowerComparison
    (hComparison : ∀ (G : RationalFunctions) (Gi : Fin 2 → RationalFunctions),
      IsPadicSymmetricGammaFactor F ψ ν.val π (lowerReversed F m h σ) G →
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i.rev) (Gi i)) →
      G = ∏ i, Gi i) :
    ∃ Gi : Fin 2 → RationalFunctions,
      (∀ i, IsPadicSymmetricGammaFactor F ψ ν.val π (σ i) (Gi i)) ∧
      IsPadicSymmetricGammaFactor F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) (∏ i, Gi i) := by
  obtain ⟨G, Gi, hG, hGi⟩ := lowerReversedGammaFactorsExist F ψ ν m h π σ hπ hσ
  have hEq := hComparison G Gi hG hGi
  rw [hEq] at hG
  exact gammaConclusion F m h σ π (fun i => (hσ i).1.1) ⟨Gi, hGi, hG⟩

/-- The remaining lower L comparison suffices with the published existence
theorems. Its polynomial equation is transported without changing Q or e. -/
theorem lConclusion_of_lowerComparison
    (hComparison : ∀ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π (lowerReversed F m h σ) P →
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i.rev) (Pi i)) →
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P) :
    ∃ (P : ℂ[X]) (Pi : Fin 2 → ℂ[X]),
      IsPadicSymmetricLPolynomial F ψ ν.val π
        (F.canonicalNormalizedProductInduced (succBlockShape m h) σ) P ∧
      (∀ i, IsPadicSymmetricLPolynomial F ψ ν.val π (σ i) (Pi i)) ∧
      ∃ (Q : ℂ[X]) (e : ℕ), X ^ e * ∏ i, Pi i = Q * P := by
  obtain ⟨P, Pi, hP, hPi⟩ := lowerReversedLPolynomialsExist F ψ ν m h π σ hπ hσ
  exact lConclusion F m h σ π (fun i => (hσ i).1.1)
    ⟨P, Pi, hP, hPi, hComparison P Pi hP hPi⟩

end Langlands.RankinSelberg.DominantRankTransport
