import Langlands.Representation.GodementJacquet.FunctionalEquationDescentStatement
import Langlands.Representation.RankinSelberg.NormalizedGeneratorExistenceProof
import Langlands.Representation.RankinSelberg.RationalGammaComparison
import Langlands.HarmonicAnalysis.RectangularFourierEquiv

/-! # Descent of full matrix functional-equation data -/

noncomputable section

namespace Langlands.GodementJacquet

open MeasureTheory HarmonicAnalysis RankinSelberg

universe uF uV uW

/-- Full normalized matrix equation data descend to an included coefficient
family whose two Laurent value spans contain one. -/
theorem normalizedMatrixFunctionalEquationDescent :
    NormalizedMatrixFunctionalEquationDescentStatement.{uF,uV,uW} := by
  intro F _ _ _ _ _ _ _ _ n _ V _ _ W _ _ q ψ ν abv μ σ τ
    hq hsd hincl hone honeDual P PDual c m hdata
  have hvalues : matrixRationalValues q abv μ τ ⊆ matrixRationalValues q abv μ σ := by
    rintro R ⟨Φ, f, hR⟩
    exact ⟨Φ, ⟨f.val, hincl f.property⟩, hR⟩
  have hvaluesDual :
      iotaMatrixRationalValues q abv μ τ ⊆ iotaMatrixRationalValues q abv μ σ := by
    rintro R ⟨Φ, f, hR⟩
    exact ⟨Φ, ⟨f.val, hincl f.property⟩, hR⟩
  have hP : IsNormalizedGenerator (matrixRationalValues q abv μ σ) P := hdata.1.2.2
  have hPDual : IsNormalizedGenerator (iotaMatrixRationalValues q abv μ σ) PDual :=
    hdata.2.1.2.2
  have hden : HasCommonDenominator (matrixRationalValues q abv μ τ) := by
    obtain ⟨d, hd, hclear⟩ := hP.hasCommonDenominator
    exact ⟨d, hd, fun R hR => hclear R (hvalues hR)⟩
  have hdenDual : HasCommonDenominator (iotaMatrixRationalValues q abv μ τ) := by
    obtain ⟨d, hd, hclear⟩ := hPDual.hasCommonDenominator
    exact ⟨d, hd, fun R hR => hclear R (hvaluesDual hR)⟩
  obtain ⟨Q, hQ⟩ := normalizedGeneratorExistence _ hden hone
  obtain ⟨QDual, hQDual⟩ := normalizedGeneratorExistence _ hdenDual honeDual
  have htarget : MatrixAnalyticAssertions q abv μ τ Q := by
    refine ⟨?_, ?_, hQ⟩
    · obtain ⟨b, hb⟩ := hdata.1.1
      exact ⟨b, fun Φ f => hb Φ ⟨f.val, hincl f.property⟩⟩
    · intro Φ f
      exact hdata.1.2.1 Φ ⟨f.val, hincl f.property⟩
  have htargetDual : IotaMatrixAnalyticAssertions q abv μ τ QDual := by
    refine ⟨?_, ?_, hQDual⟩
    · obtain ⟨b, hb⟩ := hdata.2.1.1
      exact ⟨b, fun Φ f => hb Φ ⟨f.val, hincl f.property⟩⟩
    · intro Φ f
      exact hdata.2.1.2.1 Φ ⟨f.val, hincl f.property⟩
  have hq0 : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  let δ : ℂˣ := Units.mk0 (q : ℂ)⁻¹ (inv_ne_zero hq0)
  have hδ : (δ : ℂ) = (q : ℂ)⁻¹ := rfl
  let G := rationalGammaExpression δ c m P PDual
  let T := rectangularFourierEquiv ψ ν (n + 1) (n + 1) hsd
  have hfourier : ∀ Φ : MatrixTestFunction n F,
      MatrixFourierPair ψ ν Φ (T Φ) ∧
      ∀ f : biSmoothMatrixCoefficients τ, ∀ R RDual : RationalFunctions,
        HasShiftedRationalValue q abv μ Φ f.val R →
        HasShiftedRationalValue q abv μ (T Φ) (coefficientIota f.val) RDual →
        GammaFunctionalEquation q 1 0 G R RDual := by
    intro Φ
    obtain ⟨ΦHat, hpair, heq⟩ := hdata.2.2 Φ
    have hHat : ΦHat = T Φ := by
      apply Hecke.TestFunction.ext
      intro x
      exact (hpair x).2.trans
        (rectangularFourierEquiv_apply ψ ν (n + 1) (n + 1) hsd Φ x).symm
    subst ΦHat
    refine ⟨hpair, ?_⟩
    intro f R RDual hR hRDual
    apply RationalGammaComparison.gammaFunctionalEquation_of_rational_identity hq hδ
    exact (heq ⟨f.val, hincl f.property⟩ R RDual hR hRDual).rational_gamma_identity
      hq hδ hPDual.polynomial_ne_zero
  have hST : ∀ R ∈ matrixRationalValues q abv μ τ,
      ∃ RDual ∈ iotaMatrixRationalValues q abv μ τ,
        GammaFunctionalEquation q 1 0 G R RDual := by
    rintro R ⟨Φ, f, hR⟩
    obtain ⟨RDual, hRDual⟩ := htargetDual.2.1 (T Φ) f
    exact ⟨RDual, ⟨T Φ, f, hRDual⟩, (hfourier Φ).2 f R RDual hR hRDual⟩
  have hTS : ∀ RDual ∈ iotaMatrixRationalValues q abv μ τ,
      ∃ R ∈ matrixRationalValues q abv μ τ,
        GammaFunctionalEquation q 1 0 G R RDual := by
    rintro RDual ⟨Ψ, f, hRDual⟩
    obtain ⟨R, hR⟩ := htarget.2.1 (T.symm Ψ) f
    refine ⟨R, ⟨T.symm Ψ, f, hR⟩, (hfourier (T.symm Ψ)).2 f R RDual hR ?_⟩
    simpa only [T.apply_symm_apply] using hRDual
  obtain ⟨d, a, hnormalize⟩ := gammaNormalization_of_incidence hq 1 0 G
    (matrixRationalValues q abv μ τ) (iotaMatrixRationalValues q abv μ τ)
    Q QDual hQ hQDual hST hTS
  refine ⟨Q, QDual, d, a, htarget, htargetDual, ?_⟩
  intro Φ
  exact ⟨T Φ, (hfourier Φ).1, fun f R RDual hR hRDual =>
    hnormalize R RDual ((hfourier Φ).2 f R RDual hR hRDual)⟩

end Langlands.GodementJacquet
