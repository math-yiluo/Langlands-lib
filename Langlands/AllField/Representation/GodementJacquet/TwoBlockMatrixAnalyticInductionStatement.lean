import Langlands.Representation.GodementJacquet.TwoBlockMatrixAnalyticInductionStatement
import Langlands.AllField.HarmonicAnalysis.PadicRowFourierCutoffStatement
import Langlands.AllField.Representation.GodementJacquet.AnalyticData
import Langlands.AllField.Representation.RankinSelberg.MultiplicativityStatement
/-!
# Conditional two-block matrix analytic induction

Godement--Jacquet 1972, Theorem 3.4, printed pages 36--45, for two blocks of
split general linear groups over a canonical p-adic field, in the transpose
Fourier convention of JPS 1979, printed page 177. This module only states the
analytic and product-generator part, conditionally on supplied block data.
-/

namespace Langlands.AllField.GodementJacquet
open Langlands.GodementJacquet hiding TwoBlockMatrixAnalyticInductionStatement
open Langlands.AllField.GodementJacquet

open Langlands.HarmonicAnalysis

universe uF uV

/-- If two admissible blocks with scalar central quasicharacters carry
normalized matrix functional-equation data for one self-dual measure, then the
actual normalized induced representation satisfies the matrix analytic
assertions with generator `1 / ∏ i, Pi i`, and its inverse-transpose
coefficients satisfy them with generator `1 / ∏ i, PDual i`. -/
def TwoBlockMatrixAnalyticInductionStatement : Prop :=
  ∀ (F : Type uF) [Field F] [TopologicalSpace F] [ValuativeRel F] [IsNonarchimedeanLocalField F],
    letI := IsTopologicalAddGroup.rightUniformSpace F
    letI := isUniformAddGroup_of_addCommGroup (G := F)
    letI := rowFourierCutoff_nonarchimedean (K := F)
    letI := borel F
    letI : BorelSpace F := ⟨rfl⟩
    ∀ (t : ℕ) (m : Fin 2 → ℕ) (h : ∑ i, (m i + 1) = t + 1)
      (V : Fin 2 → Type uV) [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
      (σ : ∀ i, Representation ℂ (Langlands.GeneralLinear (m i + 1) F) (V i))
      (ψ : UnitaryAdditiveCharacter F) (ν : AdditiveHaarMeasure F),
      IsSelfDual ψ ν →
      ∀ ω : Fin 2 → Quasicharacter F,
      (∀ i, Classification.HasGLCentralCharacter F (m i + 1) (σ i)
        (ω i : Fˣ →* ℂˣ)) →
      (∀ i, IsSmooth (σ i)) →
      (∀ i, IsAdmissible (σ i)) →
      ∀ (Pi PDual : Fin 2 → Polynomial ℂ) (c : Fin 2 → ℂˣ) (a : Fin 2 → ℤ),
      (∀ i, Langlands.AllField.GodementJacquet.Padic.NormalizedMatrixFunctionalEquationData F ψ ν (σ i)
        (Pi i) (PDual i) (c i) (a i)) →
      Langlands.AllField.GodementJacquet.Padic.MatrixAnalyticAssertions F
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
          (∏ i, Pi i) ∧
        Langlands.AllField.GodementJacquet.Padic.IotaMatrixAnalyticAssertions F
          ((⟨⟩ : LocalFieldData F).normalizedProductInduced (RankinSelberg.succBlockShape m h) σ)
          (∏ i, PDual i)

end Langlands.AllField.GodementJacquet
