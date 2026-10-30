import Langlands.Representation.GodementJacquet.AnalyticData
import Langlands.Representation.Induction.BlockFactors
import Langlands.Representation.RankinSelberg.MultiplicativityStatement
import Langlands.Representation.Classification.ConstituentCompatibility
import Langlands.HarmonicAnalysis.PadicRowFourierCutoffStatement

/-!
# Conditional two-block matrix analytic induction

Godement--Jacquet 1972, Theorem 3.4, printed pages 36--45, for two blocks of
split general linear groups over a canonical p-adic field, in the transpose
Fourier convention of JPS 1979, printed page 177. This module only states the
analytic and product-generator part, conditionally on supplied block data.
-/

namespace Langlands.GodementJacquet

open HarmonicAnalysis

universe uF uV

/-- If two admissible blocks with scalar central quasicharacters carry
normalized matrix functional-equation data for one self-dual measure, then the
actual normalized induced representation satisfies the matrix analytic
assertions with generator `1 / ∏ i, Pi i`, and its inverse-transpose
coefficients satisfy them with generator `1 / ∏ i, PDual i`. -/
def TwoBlockMatrixAnalyticInductionStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    letI := F.canonicalTopologicalData.topology
    letI := F.canonicalTopologicalData.valuativeRel
    letI := F.canonicalTopologicalData.localField
    letI := IsTopologicalAddGroup.rightUniformSpace F.Carrier
    letI := isUniformAddGroup_of_addCommGroup (G := F.Carrier)
    letI := rowFourierCutoff_nonarchimedean (K := F.Carrier)
    letI := borel F.Carrier
    letI : BorelSpace F.Carrier := ⟨rfl⟩
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F.Carrier) (V i))
      (ψ : UnitaryAdditiveCharacter F.Carrier) (ν : AdditiveHaarMeasure F.Carrier),
      IsSelfDual ψ ν →
      ∀ ω : Fin 2 → Quasicharacter F.Carrier,
      (∀ i, Classification.HasGLCentralCharacter F.Carrier (m i + 1) (σ i)
        (ω i : F.Carrierˣ →* ℂˣ)) →
      (∀ i, IsSmooth (σ i)) →
      (∀ i, IsAdmissible (σ i)) →
      ∀ (Pi PDual : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ),
      (∀ i, Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
        (Pi i) (PDual i) (c i) (a i)) →
      Padic.MatrixAnalyticAssertions F
          (F.canonicalNormalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
          (∏ i, Pi i) ∧
        Padic.IotaMatrixAnalyticAssertions F
          (F.canonicalNormalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
          (∏ i, PDual i)

end Langlands.GodementJacquet
